(* Module de la passe de gestion des identifiants *)
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
      | x -> raise (InfoInattendu "InfoFun")
      
  (*le type que la fonction retourn*)
  (*paramètre ia : info ast*) 
  let get_type_return ia =  
        match info_ast_to_info ia with
        | InfoFun (_,t,_) -> t
        | x -> raise (InfoInattendu "InfoFun")
  (*retourne le type*)
  (*paramètre ia : info ast*) 
  let get_type ia =  
        match info_ast_to_info ia with
        | InfoVar (_,t,_,_) -> t
        | x -> raise (InfoInattendu "Infovar")

  let egalite_type t te =
    match t with
    | te -> true
    | _ -> false


(* analyse_tds_expression : AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)


(* type expression =
  (* Appel de fonction représenté par le nom de la fonction et la liste des paramètres réels *)
  | AppelFonction of string * expression list
  (* Accès à un identifiant représenté par son nom *)
  | Ident of string
  (* Booléen *)
  | Booleen of bool
  (* Entier *)
  | Entier of int
  (* Opération unaire représentée par l'opérateur et l'opérande *)
  | Unaire of unaire * expression
  (* Opération binaire représentée par l'opérateur, l'opérande gauche et l'opérande droite *)
  | Binaire of binaire * expression * expression *)

let rec analyse_type_expression e = (* failwith "todo"*)
  match e with
  | AstTds.AppelFonction (ia, le) -> let nlet = List.map analyse_type_expression le in
                                     let tr = get_type_return ia in
                                     let tpara = get_type_param ia in
                                     let nle = List.map fst nlet in
                                     let nlt = List.map snd nlet in
                                        if (tpara = nlt) then ((AppelFonction (ia, nle)), tr)
                                        else raise (TypesParametresInattendus (nlt,tpara))
  | AstTds.Ident ia -> ((Ident ia), get_type ia)
  | AstTds.Booleen n -> (Booleen n, Bool)
  | AstTds.Entier n -> (Entier n, Int)
  | AstTds.Unaire (u, e1) -> let (ne1, te1) = analyse_type_expression e1 in
                              begin match u with
                              | AstSyntax.Denominateur -> Unaire (Denominateur, ne1), te1
                              | AstSyntax.Numerateur -> Unaire (Numerateur, ne1), te1
                              end
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


  
(* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_instruction tf i =
  match i with
  | AstTds.Declaration (t, ia, e) ->
      modifier_type_info t ia;
      let (ne, te) = analyse_type_expression e in
      if (egalite_type t te) then Declaration (ia, ne)
      else raise (TypeInattendu (t, te))
  | AstTds.Affectation (n,e) ->
      let t = (get_type n) in
      let (ne,te) = analyse_type_expression e in
      if (egalite_type t te) then Affectation (n, ne)
      else raise (TypeInattendu (t, te))

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
      | None -> raise (TypeInattendu (Undefined, Int))
      | Some t -> if (t=te) then Retour ne
                  else raise (TypeInattendu (t, te))
      end
      
(* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_type_bloc tf li =
  List.map (analyse_type_instruction tf) li

let  analyse_tds_param tds (typ,nom) =
  match chercherLocalement tds nom with
  | Some _ -> raise (DoubleDeclaration nom)
  | None -> let ia = info_to_info_ast (InfoVar (nom,Undefined, 0, "") ) in
            ajouter tds nom ia;
            (typ,ia)

(* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_type_fonctionRetour (AstTds.Fonction(t,n,lp,li))  =
  (failwith "TODO")

(* analyser : AstSyntax.ast -> AstTds.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstTds.Programme (lf,b)) =
  let nlet = List.map analyse_type_fonctionRetour lf in
  let nb = analyse_type_bloc None b in
  Programme (nlet, nb)

end
