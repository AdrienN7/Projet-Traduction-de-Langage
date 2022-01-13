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
  
  (* get_type : Tds.info_ast -> typ                  *)
  (* Paramètre ia : l'info ast de la variable        *)
  (* renvoie le typ de la variable                   *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let get_type ia =  
    match info_ast_to_info ia with
    | InfoVar (_,t,_,_) -> t
    | _ -> raise (InfoInattendu "Infovar")
  (*Pour les tests de cette fonction voir passeCodeRatToTam *)





  
(* analyse_instruction : typ option -> AstType.instruction -> AstPlacement.instruction *)
(* Paramètre reg : le déplacement actuel de la pile *)
(* Paramètre dep : le pointeur d'indication de la pile *)
(* Paramètre i : l'instruction à analyser *)
(* modifie l'ast des varaibles de l'instruction avec les bons emplacements de stockage *)
let rec analyse_instruction reg dep i =
  match i with
  | AstType.Declaration (ia, _) -> let a = (getTaille (get_type ia)) in
                                   modifier_adresse_info dep reg ia;
                                   (i, dep + a)
  | AstType.TantQue (_,b) -> let _ = (analyser_bloc reg dep b) in
                             (i, dep)
  | AstType.Conditionnelle (_, bt, be) -> let _ = (analyser_bloc reg dep bt) in
                                          let _ = (analyser_bloc reg dep be) in
                                          (i, dep)
  | _ -> (i,dep)

      
(* analyse_bloc : typ option -> AstType.bloc -> AstPlacement.bloc *)
(* Paramètre reg : le déplacement actuel de la pile *)
(* Paramètre dep : le pointeur d'indication de la pile *)
(* Paramètre li : liste d'instructions à analyser *)
(* modifie l'ast des variables du bloc avec les bons emplacements de stockage *)
and analyser_bloc reg dep li =
  match li with
  | [] -> []
  | a::q -> let (ni, ndep) = (analyse_instruction reg dep a) in
            ni ::analyser_bloc reg ndep q


(* analyse_param : type * info_ast -> type * info_ast *)
(* Paramètre : liste des paramètre de la fonction *)
(* modifie l'ast des paramètre avec les bons emplacements de stockage *)
let rec analyse_param dep rlp =
  match rlp with
  | [] -> []
  | ia::q -> let t = (getTaille (get_type ia)) in
             modifier_adresse_info (dep - t) "LB" ia;
             ia::(analyse_param (dep - t) q)


(* analyse_fonctionRetour : AstType.fonction -> AstPlacement.fonction *)
(* Paramètre : l'AstTds.fonction à analyser *)
(* modifie l'ast des différentes variables de la fonction avec les bons emplacements de stockage *)

let analyser_fonction (AstType.Fonction(ia,lp,b))  =
  let nb = (analyser_bloc "LB" 3 b) in
  let nlp = analyse_param 0 (List.rev lp) in
  Fonction(ia, nlp, nb)

(* analyser : AstType.ast -> AstType.ast *)
(* Paramètre : l'AstTds à analyser *)
(* modifie l'ast des différentes variables du programme avec les bons emplacements de stockage *)

let analyser (AstType.Programme (lf,b)) =
  let nlf = List.map (analyser_fonction) lf in
  let nb = analyser_bloc "SB" 0 b in
  Programme (nlf, nb)

end
