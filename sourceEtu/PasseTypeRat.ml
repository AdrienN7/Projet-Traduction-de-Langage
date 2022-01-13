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

  
  (* get_type_param : info_ast -> typ                  *)
  (* paramètre ia : info_ast de la fonction            *)
  (* récupère les types des parametre de la fonction   *) 
  (* Erreur si Info inattendu                          *)
  let get_type_param ia =  
      match info_ast_to_info ia with
      | InfoFun (_, _, tl) -> tl
      | _ -> raise (InfoInattendu "InfoFun")

  (* test unitaire de get_type_param *)
  let%test _ = get_type_param (info_to_info_ast (InfoFun ("todo",Int,[Rat])) )  = [Rat]
  let%test_unit _ = 
  try 
    let _ =  get_type_param (info_to_info_ast (InfoVar("toto",Int,1,"SB")) )
    in raise ErreurNonDetectee
  with
  | (InfoInattendu "InfoFun") -> ()
      
  (* get_type_return : info_ast -> typ                 *)
  (* paramètre ia : info_ast de la fonction            *)
  (* récupère le type return de la fonction            *) 
  (* Erreur si Info inattendu                          *) 
  let get_type_return ia =  
        match info_ast_to_info ia with
        | InfoFun (_,t,_) -> t
        | _ -> raise (InfoInattendu "InfoFun")

  (* test unitaire de get_type_param *)
  let%test _ = get_type_return (info_to_info_ast (InfoFun ("todo",Int,[Rat])) )  = Int
  let%test_unit _ = 
  try 
    let _ =  get_type_return (info_to_info_ast (InfoVar("toto",Int,1,"SB")) )
    in raise ErreurNonDetectee
  with
  | (InfoInattendu "InfoFun") -> ()

  (* get_type : info_ast -> typ                        *)
  (* paramètre ia : info_ast de la variable            *)
  (* récupère le type de la variable                   *) 
  (* Erreur si Info inattendu                          *)
  let get_type ia =  
        match info_ast_to_info ia with
        | InfoVar (_,t,_,_) -> t
        | _ -> raise (InfoInattendu "Infovar")
  (*Pour les tests de cette fonction voir passeCodeRatToTam *)

  
  (* analyse_type_affectable : AstTds.affectable-> AstType.affectable            *)
  (* Paramètre a : l'affectable à analyser                                       *)
  (* Vérifie la bonne utilisation des type et tranforme l'AstTds.affectable      *)
  (* en une affectable de type AstType.affectable et l'affectable                *)
  (* Erreur si mauvaise utilisation des types                                    *)
  let rec analyse_type_affectable a =
    match a with
    (*Deref: renvoie la structure du deref d'astType.affectable avec l'afectable pointé et le type du pointeur *)
    | AstTds.Deref a1 -> let ap,tp = (analyse_type_affectable a1) in
                          (Deref(ap), Pointeur tp)
    (* Ident: renvoie la structure d'ident d'astType.affectable en fonction du type d'info *)
    | AstTds.Ident ia -> 
            begin  
                  match (info_ast_to_info ia) with
                  | InfoConst _ ->  (Ident(ia), Int)
                  | InfoVar _ -> (Ident(ia), (get_type ia))
                   (*le cas si dessous ne doit jamais arriver *)
                  | InfoFun (n, _, _) -> raise (MauvaiseUtilisationIdentifiant n)
                  | InfoTyp (n,_) -> raise (MauvaiseUtilisationIdentifiant n)
                  | InfoRecord _ -> failwith("TODO") (* TODO *)
                  end
    | AstTds.Acces (a,ia) -> let a1,t1 = (analyse_type_affectable a) in (Acces (a1,ia), t1) (* Tet ODO *)



(* analyse_type_expression : AstTds.expression -> AstType.expression * typ  *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des type et tranforme l'AstTds.expression
en une expression de type AstType.expression et renvoie le type de l'expression *)
(* Erreur si mauvaise utilisation des types *)
let rec analyse_type_expression e =
  match e with
  (* Appel Fonction : vérifie le bon typage des parametre et fait l'analyse des expression dansq la fonction *)
  | AstTds.AppelFonction (ia, le) -> let nlet = List.map analyse_type_expression le in
                                     let tr = get_type_return ia in
                                     let tpara = get_type_param ia in
                                     let nle = List.map fst nlet in
                                     let nlt = List.map snd nlet in
                                        (* Vérification du bon typage des paramètres *)
                                        if (tpara = nlt) then ((AppelFonction (ia, nle)), tr)
                                        else raise (TypesParametresInattendus (nlt,tpara))
  
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

  (* ajout pour les pointeurs *)

  
  | AstTds.Null -> (Null, (Pointeur Undefined))
  | AstTds.New t -> (New(t), t)
  | AstTds.Affectable a -> let s,t = (analyse_type_affectable a) in 
                           (Affectable s, t)
  | AstTds.Adresse ia -> ((Adresse ia), (get_type ia))

  (* TODO *)
  | AstTds.Enregistrement le -> (List.fold_right (fun x y -> let (e1,_) = (analyse_type_expression x) in
                                                                  begin match y with
                                                                  | Enregistrement a -> Enregistrement (e1::a)
                                                                  | _ -> raise ErreurEnregistrement
                                                                  end)
                                                le (Enregistrement [])), Undefined(* pas enocre traité *) 

(* ajouterListNomme : (string*typ) list -> string * typ -> (string*typ) list *)
(* Paramètre ltn : liste des types nommés                                    *)
(* Paramètre nt : type nommé à ajouter à la liste                            *)
(* Renvoie la liste des type nommés mis à jour                               *)                                           
let rec ajouterListNomme ltn (nt,tn) = 
    match ltn with
    | []   -> [(nt,tn)]
    | (n,t)::q -> if (n = nt) then (nt,tn)::q else (n,t)::(ajouterListNomme q (nt,tn))

(* test unitaire de ajouterListNomme *)
  let%test _ = ajouterListNomme [("todo", Int)] ("todo", Int)   = [("todo", Int)]
  let%test _ =  ajouterListNomme [] ("todo", Int)  = [("todo", Int)]
  let%test _ = ajouterListNomme [("todo", Rat)] ("todo1", Int)   = [("todo", Rat);("todo1", Int)]

(* changer_type : string -> (string*typ) list -> typ              *)
(* Paramètre ltn : liste des types nommés                         *)
(* Paramètre tn : nom du type nommé dont on veut renvoyer le type *)
(* Renvoie le type réel du type nommé                             *)
let rec changer_type tn ltn = 
  match ltn with
  | [] -> raise (Erreur_type_nomme)
  | (n,t)::q -> if (n=tn) then t 
                else (changer_type tn q)

(* test unitaire changer_type *)
 let%test _ = changer_type "todo" [("todo", Int)] = Int
let%test _ = changer_type "todo1" [("todo", Int);("todo1", Rat)] = Rat
let%test_unit _ = 
  try 
    let _ =  changer_type "todo" []   = [("todo", Int)]
    in raise ErreurNonDetectee
  with
  | (Erreur_type_nomme) -> ()


(* analyse_type_instruction : typ option -> AstTds.instruction -> AstTypeInstruction *)
(* Paramètre tf : le type attendu de l'instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des types et tranforme l'instruction de type AstTds.instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvaise utilisation des types *)
let rec analyse_type_instruction ltn tf i =
  match i with
  | AstTds.Declaration (t, ia, e) ->
      (* modifier le type ici *)
      let nt =
      begin
      match t with
      | Tident n  -> changer_type n ltn 
      | _ -> t
      end in
      modifier_type_info nt ia;
      let (ne, te) = analyse_type_expression e in
      if (est_compatible nt te) then Declaration (ia, ne)
      else raise (TypeInattendu (te, nt))
      
  | AstTds.Affectation (a,e) ->
      let s , t = (analyse_type_affectable a) in
      let (ne,te) = analyse_type_expression e in
      if (est_compatible t te) then Affectation (s, ne)
      else raise (TypeInattendu (te, t))

  (* Résolution de la surcharge sur l'affichage *)
  (* Erreur si types indéfines *)
  | AstTds.Affichage e -> 
      let (ne,te) = analyse_type_expression e in
        if (est_compatible te Int) then AffichageInt ne
        else if (est_compatible te Rat) then AffichageRat ne
        else if (est_compatible te Bool) then AffichageBool ne
        else raise (TypeInattendu (te,Undefined))

  | AstTds.Conditionnelle (c,bt,be) -> 
      let (ne,te) = analyse_type_expression c in
      if (te != Bool) then raise (TypeInattendu (te, Bool))
      else let nbt = analyse_type_bloc tf bt ltn in
           let nbe = analyse_type_bloc tf be ltn in
           Conditionnelle (ne, nbt, nbe)
  | AstTds.TantQue (c,b) -> 
      let (ne,te) = analyse_type_expression c in
      if (te != Bool) then raise (TypeInattendu (te, Bool))
      else let nb = analyse_type_bloc tf b ltn in
          TantQue (ne, nb)
  | AstTds.Retour (e) -> 
      let (ne, te) = analyse_type_expression e in
      begin match tf with
      | None -> raise RetourDansMain
      | Some t -> if (est_compatible t te) then Retour ne
                  else raise (TypeInattendu (te, t))
      end
  | AstTds.Empty -> Empty
  (* ajout pour l'operateur d'assignation *)
  | AstTds.Addition (a1,e1) -> let (na,ta) = analyse_type_affectable a1 in
                                  let (ne,te) = analyse_type_expression e1 in
                                    if ((est_compatible ta te) && (est_compatible ta Int) ) then 
                                      Affectation (na,(Binaire(PlusInt, Affectable na, ne)))
                                    else if ((est_compatible ta te) && (est_compatible ta Rat)) then 
                                      Affectation (na,(Binaire(PlusRat, Affectable na, ne)))
                                    else raise (TypeInattendu(ta, te))
  | AstTds.Typedeflocal (n,t) -> Typedeflocal (n,t)

    
                                      


      
(* analyse_type_bloc : typ option -> AstTds.bloc -> AstType.bloc *)
(* Paramètre tf : : le type retour attendu du bloc *)
(* Paramètre li : liste d'instructions à analyser *)
(* Paramètre ltn : liste des type nommé défini à l'exterieur du bloc *)
(* Vérifie la bonne utilisation des types et tranforme le bloc de type 
AstTds.bloc en un bloc de type AstType.bloc *)
(* Erreur si mauvaise utilisation des types *)
and analyse_type_bloc tf li ltn =
  match li with
  | [] -> []
  | i::q -> begin 
                      let i1 = (analyse_type_instruction ltn tf i ) in 
                      match i1 with
                     | Typedeflocal (n,t) -> let newltn = ajouterListNomme ltn (n,t) in
                                         (analyse_type_bloc tf q newltn)
                     | _ -> i1::(analyse_type_bloc tf q ltn)
                     end

(* analyse_type_param : type * info_ast -> type * info_ast *)
(* Paramètre : liste des paramètre de la fonction *)
(* modifie l'ast avec les bon paramètres *)
let  analyse_type_param ltn (typ,n) =
  
      match typ with
       | Tident tn  -> let nt = changer_type tn ltn in
                        modifier_type_info nt n;
                        (nt,n)
      | _ -> modifier_type_info typ n;
            (typ,n)
      

  
(* analyse_type_fonctionRetour : AstTds.fonction -> AstType.fonction *)
(* Paramètre : l'AstTds.fonction à analyser *)
(* Vérifie la bonne utilisation des type et tranforme la fonction de
type AstTds.fonction en une fonction de type AstType.fonction *)
(* Erreur si mauvaise utilisation des types *)
let analyse_type_fonctionRetour ltn (AstTds.Fonction(t,n,lp,li))  =
  let tlp = List.map (analyse_type_param ltn) lp in
  let slp = List.map (fun (a,_) -> a) tlp in
  let sn = List.map (fun (_,b) -> b) tlp in
  begin
   match t with
      | Tident tn  -> let nt = changer_type tn ltn in
                        modifier_type_fonction_info nt slp n;
                        let nli = analyse_type_bloc (Some nt) li ltn in
                        Fonction (n,sn,nli)             
      | _ -> modifier_type_fonction_info t slp n;
            let nli = analyse_type_bloc (Some t) li ltn in
            Fonction (n,sn,nli)
  end


(* analyser : AstTds.ast -> AstType.ast *)
(* Paramètre : l'AstTds à analyser *)
(* Vérifie la bonne utilisation des types et tranforme le programme
de type AstTds.ast en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des types *)
let analyser (AstTds.Programme (ln, lf,b)) =
  (* liste assaciant le non au type *)
  let ltn = (List.fold_right (fun  (AstTds.Typedefglobal (a,b)) y ->  (a,b)::y) ln []) in
  let nlet = List.map (analyse_type_fonctionRetour ltn) lf  in
  let nb = analyse_type_bloc None b ltn in
  Programme (nlet, nb)

end
