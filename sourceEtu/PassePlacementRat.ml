(* Module de la passe de gestion du typage *)
module PassePlacementRat : Passe.Passe with type t1 = Ast.AstType.programme and type t2 = Ast.AstPlacement.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstPlacement
  open Type

  type t1 = Ast.AstType.programme
  type t2 = Ast.AstPlacement.programme
  
  (*retourne le type*)
  (*paramètre ia : info ast*) 
  let get_type ia =  
    match info_ast_to_info ia with
    | InfoVar (_,t,_,_) -> t
    | x -> raise (InfoInattendu "Infovar")

  let get_taille t =
    match t with
    | Rat -> 2
    | _ -> 1


(* analyse_placement_expression : AstType.expression -> AstPlacement.expression * typ *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des type et tranforme l'AstTds.expression
en une expression de type AstType.expression et renvoie le type de l'expression *)
(* Erreur si mauvaise utilisation des types *)


  
(* analyse_type_instruction : typ option -> AstTds.instruction -> AstTypeInstruction *)
(* Paramètre tf : le type attendu de l'instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des types et tranforme l'instruction de type AstTds.instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvaise utilisation des types *)
let rec analyse_instruction reg dep i =
  match i with
  | AstType.Declaration (ia, e) -> let a = (get_taille (get_type ia)) in
                                   modifier_adresse_info dep reg ia;
                                   (i, dep + a)
  | AstType.TantQue (e,b) -> let nb = (analyser_bloc reg dep b) in
                             (i, dep)
  | AstType.Conditionnelle (e, bt, be) -> let _ = (analyser_bloc reg dep bt) in
                                          let _ = (analyser_bloc reg dep bt) in
                                          (i, dep)
  | _ -> (i,dep)

      
(* analyse_type_bloc : typ option -> AstTds.bloc -> AstType.bloc *)
(* Paramètre tf : : le type retour attendu du bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des types et tranforme le bloc de type 
AstTds.bloc en un bloc de type AstType.bloc *)
(* Erreur si mauvaise utilisation des types *)
and analyser_bloc reg dep li =
  match li with
  | [] -> []
  | a::q -> let (ni, ndep) = (analyse_instruction reg dep a) in
            ni ::analyser_bloc reg ndep q


(* analyse_type_param : type * info_ast -> type * info_ast *)
(* Paramètre : liste des paramètre de la fonction *)
(* modifie l'ast avec les bon paramètres *)
let rec analyse_param dep rlp =
  match rlp with
  | [] -> []
  | ia::q -> let t = (get_taille (get_type ia)) in
             modifier_adresse_info (dep - 1) "LB" ia;
             ia::(analyse_param (dep - 1) q)
(* analyse_type_fonctionRetour : AstTds.fonction -> AstType.fonction *)
(* Paramètre : l'AstTds.fonction à analyser *)
(* Vérifie la bonne utilisation des type et tranforme la fonction de
type AstTds.fonction en une fonction de type AstType.fonction *)
(* Erreur si mauvaise utilisation des types *)
let analyser_fonction (AstType.Fonction(ia,lp,b))  =
  let nb = (analyser_bloc "LB" 3 b) in
  let nlp = analyse_param 0 (List.rev lp) in
  Fonction(ia, nlp, nb)

(* analyser : AstTds.ast -> AstType.ast *)
(* Paramètre : l'AstTds à analyser *)
(* Vérifie la bonne utilisation des types et tranforme le programme
de type AstTds.ast en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des types *)
let analyser (AstType.Programme (lf,b)) =
  let nlf = List.map (analyser_fonction) lf in
  let nb = analyser_bloc "SB" 0 b in
  Programme (nlf, nb)

end
