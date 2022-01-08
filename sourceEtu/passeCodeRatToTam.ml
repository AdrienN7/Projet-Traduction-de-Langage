(* Module de la passe de gestion du typage *)
module PasseCodeRatToTam : Passe.Passe with type t1 = Ast.AstPlacement.programme and type t2 = string =
struct

  open Tds
  open Exceptions
  open Ast
  open AstPlacement
  open Type
  open Code

  type t1 = Ast.AstPlacement.programme
  type t2 = string
  
  (*retourne le type*)
  (*paramètre ia : info ast*) 
  
  let get_type ia =  
    match (info_ast_to_info ia) with
    | InfoVar (_,t,_,_) -> t
    | _ -> raise (InfoInattendu "Infovar1")

  let taille_variables i = 
    match i with
    | AstType.Declaration (n, _) -> (getTaille (get_type n))
    | _ -> 0

  
  let get_dep_reg ia =
    match (info_ast_to_info ia) with
    | InfoVar (_,_,dep,reg) -> (dep,reg)
    | _ -> raise (InfoInattendu "Infovar2")


let rec analyser_tam_affectable a iOUe pointeur =
  match a with
    | AstType.Deref a1 -> (analyser_tam_affectable a1 iOUe true)
    | AstType.Ident ia -> match (info_ast_to_info ia) with
                          | InfoVar (_,t,dep,reg) -> 

                                          if (iOUe && (not pointeur)) then
                                            "LOAD ("^(string_of_int (getTaille (get_type ia)))^") "
                                            ^(string_of_int dep)^"["^reg^"]\n"
                                            else if ((not iOUe) && (not pointeur)) then
                                            "STORE ("^(string_of_int (getTaille t))^") "^(string_of_int dep)^"["^reg^"]\n"
                                            else if (iOUe && pointeur) then "LOADI ("^(string_of_int (getTaille (get_type ia)))^")\n"
                                            else "LOAD ("^(string_of_int (getTaille (get_type ia)))^") "
                                            ^(string_of_int dep)^"["^reg^"]\n"
                                            ^"STOREI ("^string_of_int(getTaille t)^")\n" (*faux pour le type RAT *)
                          | InfoConst (t,nb) -> "LOADL "^(string_of_int nb)^"\n"
                          | InfoFun _ -> ""


and analyser_tam_expression e =
  match e with
  | AstType.AppelFonction (n,b) -> let nom = begin 
                                            match info_ast_to_info n with
                                            | InfoFun(nf, _, _) -> nf
                                            | _ -> raise (InfoInattendu "infoVar3")
                                            end in
                                            (List.fold_right (fun x y -> (analyser_tam_expression x)^"\n"^y) b "")
                                  ^"CALL (SB) "^nom^"\n"
  | Booleen (bool) -> if bool then "LOADL 1\n" else "LOADL 0\n"
  | Entier (ent) -> "LOADL "^(string_of_int ent)^"\n"
  | Unaire (u,exp) -> let typa = begin match u with
                                 | Denominateur -> "POP (1) 1\n"
                                 | Numerateur -> "POP (0) 1\n"
                                  end in
                      (analyser_tam_expression exp)^"\n"
                      ^typa
  | Binaire (b, e1, e2) -> let typa = begin match b with
                            | Fraction -> ""
                            | Inf -> "SUBR ILss"
                            | PlusInt -> "SUBR IAdd"
                            | PlusRat -> "CALL (SB) RAdd"
                            | MultInt -> "SUBR IMul"
                            | MultRat -> "CALL (SB) RMul"
                            | EquInt -> "SUBR IEq"
                            | EquBool -> "SUBR IEq"
                            end in
                          (analyser_tam_expression e1)^"\n"
                           ^(analyser_tam_expression e2)^"\n"
                           ^typa^"\n"
      (* ajout pour les pointeurs *)
  | Null -> "0 \n"
  | New t -> "LOADL "^(string_of_int (getTaille t))^"\n" 
             ^"SUBR MAlloc \n"
  | Affectable (a,t) -> (analyser_tam_affectable a true false)
  | Adresse ia -> let (dep,reg) = (get_dep_reg ia) in
                  "LOADA "^(string_of_int dep)^"["^reg^"]\n"

                       

let rec analyse_tam_instruction i ttr tparam =
  match i with
  | AstType.Declaration (n, e) -> let taille = (getTaille (get_type n)) in
                          let (dep,reg) = (get_dep_reg n) in
"PUSH "^(string_of_int taille)^"\n"
^(analyser_tam_expression e)
^"STORE ("^(string_of_int taille)^") "^(string_of_int dep)^"["^reg^"]\n"


  | Affectation (a, e) -> (analyser_tam_expression e)^"\n"^(analyser_tam_affectable a false false)
  (*let (dep,reg) = (get_dep_reg n) in
                          (analyser_tam_expression e)^"\n"^"STORE ("^(string_of_int (getTaille (get_type n)))^") "^(string_of_int dep)^"["^reg^"]\n"
*)

  | AffichageInt e -> (analyser_tam_expression e)^"\n"^"SUBR IOut\n"
  | AffichageRat e -> (analyser_tam_expression e)^"\n"^"CALL (SB) ROut\n"
  | AffichageBool e -> (analyser_tam_expression e)^"\n"^"SUBR Bout\n"
  | Conditionnelle (e,bt,be) -> let etiquetElse = (getEtiquette ()) in
                                let etiquetFin = (getEtiquette ()) in
                                (analyser_tam_expression e)^"\n"^"JUMPIF (0) "^etiquetElse^"\n"
                                ^(analyser_tam_bloc bt ttr tparam)
                                ^"JUMP "^etiquetFin^"\n"
                                ^etiquetElse^"\n"
                                ^(analyser_tam_bloc be ttr tparam)
                                ^etiquetFin^"\n"
  | TantQue (e,b) -> let etiquetWhile = (getEtiquette ()) in
                      let etiquetFin = (getEtiquette ()) in
                      etiquetWhile^"\n"
                      ^(analyser_tam_expression e)^"\n"
                      ^"JUMPIF (0) "^etiquetFin^"\n"
                      ^(analyser_tam_bloc b ttr tparam)^"\n"
                      ^"JUMP "^etiquetWhile^"\n"
                      ^etiquetFin^"\n"
  | Retour e -> (analyser_tam_expression e)^"\n"
                ^"RETURN ("^(string_of_int ttr)^") "^(string_of_int tparam)^"\n"
  | Empty -> ""


      

and analyser_tam_bloc li ttr tparam =
let (bloc_tam, tp) = (List.fold_right (fun x (y,w) -> (analyse_tam_instruction x ttr tparam)^y,(taille_variables x) + w) li ("",0)) in
bloc_tam
^"POP (0) "
^(string_of_int (tp))
^"\n"


(* analyse_type_fonctionRetour : AstTds.fonction -> AstType.fonction *)
(* Paramètre : l'AstTds.fonction à analyser *)
(* Vérifie la bonne utilisation des type et tranforme la fonction de
type AstTds.fonction en une fonction de type AstType.fonction *)
(* Erreur si mauvaise utilisation des types *)
let analyser_tam_fonction (Fonction(ia,_,b))  = 
  match (info_ast_to_info ia) with
  | InfoFun (nf, tf, lpf) -> let tparams = (List.fold_right (fun x y -> (getTaille x) + y) lpf 0) in
                            nf^"\n"
                            ^(analyser_tam_bloc b (getTaille tf) tparams)^"\n"
                            ^"HALT\n"
  | _ -> raise (InfoInattendu "InfoFun")



let analyser (Programme (lf,b)) =
  ""^(getEntete ())^(String.concat "\n\n" (List.map analyser_tam_fonction lf))^
"main\n"^
(analyser_tam_bloc b 0 0)^
"HALT\n"

end
