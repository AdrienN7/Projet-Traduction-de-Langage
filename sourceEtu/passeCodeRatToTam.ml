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

let analyser_tam_expression e =
  match e with
  | AstType.AppelFonction (n,b) -> ""
  | Ident (id_info) -> ""
  | Booleen (bool) -> ""
  | Entier (ent) -> (string_of_int ent)
  | Unaire (u,exp) -> ""
  | Binaire (b, e1, e2) -> ""

let rec analyse_tam_instruction i =
  match i with
  | AstType.Declaration (n, e) -> let taille = (get_taille (get_type n)) in
                          let (dep,reg) = (get_dep_reg n) in
"PUSH "^(string_of_int taille)^"\n"
^(analyser_tam_expression e)
^"STORE "^(string_of_int taille)^" "^(string_of_int dep)^"["^reg^"]\n"

  | Affectation (n, e) -> ""
  | AffichageInt e -> ""
  | AffichageRat e -> ""
  | AffichageBool e -> ""
  | Conditionnelle (e,bt,be) -> ""
  | TantQue (e,b) -> ""
  | Retour e -> ""
  | Empty -> ""


      

and analyser_tam_bloc li =
(List.fold_right (fun x y -> (analyse_tam_instruction x)^"\n"^y) li "")
^"POP (O) "
^(string_of_int (taille_variables_locales li))
^"\n\n"


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
(analyser_tam_bloc b)^
"HALT\n" 

end
