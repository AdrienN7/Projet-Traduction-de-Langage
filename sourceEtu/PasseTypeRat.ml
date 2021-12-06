(* Module de la passe de gestion du typage *)
module PasseTypeRat : Passe.Passe with type t1 = Ast.AstTds.programme and type t2 = Ast.AstType.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstType
  open Type

  type t1 = Ast.AstTds.programme
  type t2 = Ast.AstType.programme
  
  (*list des types de param*)
  (*paramètre ia : info ast*) 
  let get_type_param ia =  
      match info_ast_to_info ia with
      | InfoFun (_, _, tl) -> tl
      | _ -> raise (InfoInattendu "InfoFun")
      
  (*le type que la fonction retourne*)
  (*paramètre ia : info ast*) 
  let get_type_return ia =  
        match info_ast_to_info ia with
        | InfoFun (_,t,_) -> t
        | _ -> raise (InfoInattendu "InfoFun")
  (*retourne le type*)
  (*paramètre ia : info ast*) 
  let get_type ia =  
        match info_ast_to_info ia with
        | InfoVar (_,t,_,_) -> t
        | _ -> raise (InfoInattendu "Infovar")


(* analyse_type_expression : AstTds.expression -> AstType.expression * typ *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des type et tranforme l'AstTds.expression
en une expression de type AstType.expression et renvoie le type de l'expression *)
(* Erreur si mauvaise utilisation des types *)


let rec analyse_type_expression e =
  match e with
  | AstTds.AppelFonction (ia, le) -> let nlet = List.map analyse_type_expression le in
                                     let tr = get_type_return ia in
                                     let tpara = get_type_param ia in
                                     let nle = List.map fst nlet in
                                     let nlt = List.map snd nlet in
                                        (* Vérification du bon typage des paramètres *)
                                        if (tpara = nlt) then ((AppelFonction (ia, nle)), tr)
                                        else raise (TypesParametresInattendus (nlt,tpara))
  | AstTds.Ident ia -> ((Ident ia), get_type ia)
  | AstTds.Booleen n -> (Booleen n, Bool)
  | AstTds.Entier n -> (Entier n, Int)

   (* Résolution de la surcharge sur les opérateurs unaires *)
  (* Erreur si type et opération incomaptibles *)
  | AstTds.Unaire (u, e1) -> let (ne1, te1) = analyse_type_expression e1 in
                              begin match u with
                              | AstSyntax.Denominateur -> if (est_compatible te1 Rat) then Unaire (Denominateur, ne1), Int
                                                          else raise (TypeInattendu (te1, Rat))
                              | AstSyntax.Numerateur -> if (est_compatible te1 Rat) then Unaire (Numerateur, ne1), Int
                                                        else raise (TypeInattendu (te1, Rat))
                              end
  
  (* Résolution de la surcharge sur les opérateurs binaires *)
  (* Erreur si types et opération incomaptibles *)
  | AstTds.Binaire (b, e1, e2) -> begin match b, analyse_type_expression e1, analyse_type_expression e2 with
                                        | AstSyntax.Fraction, (a,Int), (c,Int) -> (Binaire (Fraction, a, c) , Rat)
                                        | AstSyntax.Fraction, (_,a), (_,c)-> raise (TypeBinaireInattendu (Fraction, a, c))
                                        | AstSyntax.Inf, (a,Int), (c,Int) -> (Binaire (Inf, a, c), Bool)
                                        | AstSyntax.Inf, (_,a), (_,c)-> raise (TypeBinaireInattendu (Inf,a,c))
                                        | AstSyntax.Plus, (a,Int), (c,Int) -> (Binaire(PlusInt, a, c), Int)
                                        | AstSyntax.Plus, (a,Rat), (c,Rat) -> (Binaire(PlusRat, a, c), Rat)
                                        | AstSyntax.Mult, (a,Int), (c,Int) -> (Binaire(MultInt, a, c), Int)
                                        | AstSyntax.Mult, (a,Rat), (c,Rat) -> (Binaire(MultRat, a, c), Rat)
                                        | AstSyntax.Equ, (a,Int), (c,Int) -> (Binaire(EquInt, a, c), Bool)
                                        | AstSyntax.Equ, (a,Bool), (c,Bool) -> (Binaire(EquBool, a, c), Bool)
                                        | AstSyntax.Plus, (_,a), (_,b)-> raise (TypeBinaireInattendu (Plus,a, b))
                                        | AstSyntax.Mult, (_,a), (_,b)-> raise (TypeBinaireInattendu (Mult,a, b))
                                        | AstSyntax.Equ, (_,a), (_,b)-> raise (TypeBinaireInattendu (Equ,a,b))
                                    
                                      end


  
(* analyse_type_instruction : typ option -> AstTds.instruction -> AstTypeInstruction *)
(* Paramètre tf : le type attendu de l'instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des types et tranforme l'instruction de type AstTds.instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvaise utilisation des types *)
let rec analyse_type_instruction tf i =
  match i with
  | AstTds.Declaration (t, ia, e) ->
      modifier_type_info t ia;
      let (ne, te) = analyse_type_expression e in
      if (t = te) then Declaration (ia, ne)
      else raise (TypeInattendu (te, t))
  | AstTds.Affectation (n,e) ->
      let t = (get_type n) in
      let (ne,te) = analyse_type_expression e in
      if (t = te) then Affectation (n, ne)
      else raise (TypeInattendu (te, t))

  (* Résolution de la surcharge sur l'affichage *)
  (* Erreur si types indéfines *)
  | AstTds.Affichage e -> 
      let (ne,te) = analyse_type_expression e in
        begin match te with
        | Int -> AffichageInt ne
        | Rat -> AffichageRat ne
        | Bool -> AffichageBool ne
        | _ -> raise (TypeInattendu (te,Undefined ))
        end
  | AstTds.Conditionnelle (c,bt,be) -> 
      let (ne,te) = analyse_type_expression c in
      if (te != Bool) then raise (TypeInattendu (te, Bool))
      else let nbt = analyse_type_bloc tf bt in
           let nbe = analyse_type_bloc tf be in
           Conditionnelle (ne, nbt, nbe)
  | AstTds.TantQue (c,b) -> 
      let (ne,te) = analyse_type_expression c in
      if (te != Bool) then raise (TypeInattendu (te, Bool))
      else let nb = analyse_type_bloc tf b in
          TantQue (ne, nb)
  | AstTds.Retour (e) -> 
      let (ne, te) = analyse_type_expression e in
      begin match tf with
      | None -> raise RetourDansMain
      | Some t -> if (t=te) then Retour ne
                  else raise (TypeInattendu (te, t))
      end
  | AstTds.Empty -> Empty
      
(* analyse_type_bloc : typ option -> AstTds.bloc -> AstType.bloc *)
(* Paramètre tf : : le type retour attendu du bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des types et tranforme le bloc de type 
AstTds.bloc en un bloc de type AstType.bloc *)
(* Erreur si mauvaise utilisation des types *)
and analyse_type_bloc tf li =
  List.map (analyse_type_instruction tf) li

(* analyse_type_param : type * info_ast -> type * info_ast *)
(* Paramètre : liste des paramètre de la fonction *)
(* modifie l'ast avec les bon paramètres *)
let  analyse_type_param  (typ,n) =
  modifier_type_info typ n;
  (typ,n)
(* analyse_type_fonctionRetour : AstTds.fonction -> AstType.fonction *)
(* Paramètre : l'AstTds.fonction à analyser *)
(* Vérifie la bonne utilisation des type et tranforme la fonction de
type AstTds.fonction en une fonction de type AstType.fonction *)
(* Erreur si mauvaise utilisation des types *)
let analyse_type_fonctionRetour (AstTds.Fonction(t,n,lp,li))  =
  let tlp = List.map (analyse_type_param) lp in
  let slp = List.map (fun (a,_) -> a) tlp in
  let sn = List.map (fun (_,b) -> b) tlp in
  modifier_type_fonction_info t slp n;
  let nli = analyse_type_bloc (Some t) li in
  Fonction (n,sn,nli)

(* analyser : AstTds.ast -> AstType.ast *)
(* Paramètre : l'AstTds à analyser *)
(* Vérifie la bonne utilisation des types et tranforme le programme
de type AstTds.ast en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des types *)
let analyser (AstTds.Programme (lf,b)) =
  let nlet = List.map analyse_type_fonctionRetour lf in
  let nb = analyse_type_bloc None b in
  Programme (nlet, nb)

end
