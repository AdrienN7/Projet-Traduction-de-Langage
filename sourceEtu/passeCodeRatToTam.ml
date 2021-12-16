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
    | _ -> raise (InfoInattendu "Infovar")

  let get_taille t =
    match t with
    | Rat -> 2
    | _ -> 1
    
  let taille_variables_locales li = 0

  
  let get_dep_reg ia =
    match (info_ast_to_info ia) with
    | InfoVar (_,_,dep,reg) -> (dep,reg)
    | _ -> raise (InfoInattendu "Infovar")

let rec analyser_tam_expression e =
  match e with
  | AstType.AppelFonction (n,b) -> ""
  | Ident (id_info) -> let (dep,reg) = (get_dep_reg id_info) in
                       "LOAD "^(string_of_int (get_taille (get_type id_info)))^" "
                       ^(string_of_int dep)^"["^reg^"]\n"
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
                           ^typa

let rec analyse_tam_instruction i ttr tparam =
  match i with
  | AstType.Declaration (n, e) -> let taille = (get_taille (get_type n)) in
                          let (dep,reg) = (get_dep_reg n) in
"PUSH "^(string_of_int taille)^"\n"
^(analyser_tam_expression e)
^"STORE "^(string_of_int taille)^" "^(string_of_int dep)^"["^reg^"]\n"

  | Affectation (n, e) -> let (dep,reg) = (get_dep_reg n) in
                          (analyser_tam_expression e)^"\n"^"STORE "^(string_of_int (get_taille (get_type n)))^" "^(string_of_int dep)^"["^reg^"]\n"
  | AffichageInt e -> (analyser_tam_expression e)^"\n"^"SUBR IOut\n"
  | AffichageRat e -> (analyser_tam_expression e)^"\n"^"CALL (SB) ROut\n"
  | AffichageBool e -> (analyser_tam_expression e)^"\n"^"SUBR Bout\n"
  | Conditionnelle (e,bt,be) -> let etiquetElse = (getEtiquette ()) in
                                let etiquetFin = (getEtiquette ()) in
                                (analyser_tam_expression e)^"\n"^"JUMPIF (1) "^etiquetElse^"\n"
                                ^(analyser_tam_bloc bt 0 0)
                                ^"JUMP "^etiquetFin^"\n"
                                ^etiquetElse^"\n"
                                ^(analyser_tam_bloc be 0 0)
                                ^etiquetFin^"\n"
  | TantQue (e,b) -> let etiquetWhile = (getEtiquette ()) in
                      let etiquetFin = (getEtiquette ()) in
                      etiquetWhile^"\n"
                      ^(analyser_tam_expression e)^"\n"
                      ^"JUMPIF (0) "^etiquetFin^"\n"
                      ^(analyser_tam_bloc b 0 0)^"\n"
                      ^"JUMP "^etiquetWhile^"\n"
                      ^etiquetFin
  | Retour e -> (analyser_tam_expression e)^"\n"
                ^"RETURN "^(string_of_int ttr)^" "^(string_of_int tparam)
  | Empty -> ""


      

and analyser_tam_bloc li ttr tparam =
(List.fold_right (fun x y -> (analyse_tam_instruction x ttr tparam)^y,taille_variables) li "")
^"POP (0) "
^(string_of_int (taille_variables_locales li))
^"\n"


(* analyse_type_param : type * info_ast -> type * info_ast *)
(* Paramètre : liste des paramètre de la fonction *)
(* modifie l'ast avec les bon paramètres *)
let rec analyse_tam_param dep rlp = ""

(* analyse_type_fonctionRetour : AstTds.fonction -> AstType.fonction *)
(* Paramètre : l'AstTds.fonction à analyser *)
(* Vérifie la bonne utilisation des type et tranforme la fonction de
type AstTds.fonction en une fonction de type AstType.fonction *)
(* Erreur si mauvaise utilisation des types *)
let analyser_tam_fonction (Fonction(ia,lp,b))  = ""



let analyser (Programme (lf,b)) =
  ""^(getEntete ())^(String.concat "\n\n" (List.map analyser_tam_fonction lf))^
"main\n"^
(analyser_tam_bloc b 0 0)^
"HALT\n"

end
