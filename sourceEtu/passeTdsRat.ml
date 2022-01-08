(* Module de la passe de gestion des identifiants *)
module PasseTdsRat : Passe.Passe with type t1 = Ast.AstSyntax.programme and type t2 = Ast.AstTds.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstTds

  type t1 = Ast.AstSyntax.programme
  type t2 = Ast.AstTds.programme



  let rec analyse_tds_affectable tds modif a =
    match a with
   | AstSyntax.Deref a1 -> Deref(analyse_tds_affectable tds modif a1)
   | AstSyntax.Ident n -> 
   begin
        match (chercherGlobalement tds n) with
        | None ->  raise (IdentifiantNonDeclare n)
        | Some ia -> 
          begin  
            match (info_ast_to_info ia) with
            | InfoConst (n,_) -> if modif then raise (MauvaiseUtilisationIdentifiant n)
                                 else Ident(ia)
            | InfoVar _ -> Ident(ia)
            | InfoFun _ -> raise (MauvaiseUtilisationIdentifiant n)
          end
  
      end

(* analyse_tds_expression : AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)

let rec analyse_tds_expression tds e =
  match e with
  | AstSyntax.AppelFonction (n, li) -> 
    begin
      match (chercherGlobalement tds n) with 
         | None -> raise (IdentifiantNonDeclare n)
         | Some ia -> begin
                      match info_ast_to_info ia with
                      | InfoFun(_) -> AppelFonction (ia,(List.map (analyse_tds_expression tds) li))
                      | _ -> raise (MauvaiseUtilisationIdentifiant n)
         end
    end
  | AstSyntax.Affectable a1 -> Affectable(analyse_tds_affectable tds false a1)  
  | AstSyntax.Null -> Null 
  | AstSyntax.New t -> New (t)
  | AstSyntax.Adresse n ->
  begin
      match (chercherGlobalement tds n) with
      | None ->  raise (IdentifiantNonDeclare n)
      | Some ia -> 
        begin  
          match (info_ast_to_info ia) with
          | InfoVar _ ->  Adresse (ia)
          | _ -> raise (MauvaiseUtilisationIdentifiant n)
        end

    end     
  | AstSyntax.Booleen n -> Booleen (n)
  | AstSyntax.Entier n -> Entier (n)
  | AstSyntax.Unaire (u, e1) -> Unaire (u, (analyse_tds_expression tds e1))
  | AstSyntax.Binaire (b, e1, e2) -> Binaire (b, analyse_tds_expression tds e1, analyse_tds_expression tds e2)

  
(* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds i =
  match i with
  | AstSyntax.Declaration (t, n, e) ->
      begin
        match chercherLocalement tds n with
        | None ->
            (* L'identifiant n'est pas trouvé dans la tds locale, 
            il n'a donc pas été déclaré dans le bloc courant *)
            (* Vérification de la bonne utilisation des identifiants dans l'expression *)
            (* et obtention de l'expression transformée *) 
            let ne = analyse_tds_expression tds e in
            (* Création de l'information associée à l'identfiant *)
            let info = InfoVar (n,t, 0, "") in
            (* Création du pointeur sur l'information *)
            let ia = info_to_info_ast info in
            (* Ajout de l'information (pointeur) dans la tds *)
            ajouter tds n ia;
            (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information 
            et l'expression remplacée par l'expression issue de l'analyse *)
            Declaration (t, ia, ne) 
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale, 
            il a donc déjà été déclaré dans le bloc courant *) 
            raise (DoubleDeclaration n)
      end
  | AstSyntax.Constante (n,v) -> 
      begin
        match chercherLocalement tds n with
        | None -> 
        (* L'identifiant n'est pas trouvé dans la tds locale, 
        il n'a donc pas été déclaré dans le bloc courant *)
        (* Ajout dans la tds de la constante *)
        ajouter tds n (info_to_info_ast (InfoConst (n,v))); 
        (* Suppression du noeud de déclaration des constantes devenu inutile *)
        Empty
        | Some _ ->
          (* L'identifiant est trouvé dans la tds locale, 
          il a donc déjà été déclaré dans le bloc courant *) 
          raise (DoubleDeclaration n)
      end
  | AstSyntax.Affichage e -> 
      (* Vérification de la bonne utilisation des identifiants dans l'expression *)
      (* et obtention de l'expression transformée *)
      let ne = analyse_tds_expression tds e in
      (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
      Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) -> 
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc then *)
      let tast = analyse_tds_bloc tds t in
      (* Analyse du bloc else *)
      let east = analyse_tds_bloc tds e in
      (* Renvoie la nouvelle structure de la conditionnelle *)
      Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) -> 
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc *)
      let bast = analyse_tds_bloc tds b in
      (* Renvoie la nouvelle structure de la boucle *)
      TantQue (nc, bast)
  | AstSyntax.Retour (e) -> 
      (* Analyse de l'expression *)
      let ne = analyse_tds_expression tds e in
      Retour (ne)
  | AstSyntax.Affectation (a,e) ->
      let ne = analyse_tds_expression tds e in
      let na = analyse_tds_affectable tds true a in
      Affectation(na, ne)

      
(* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds li =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale 
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in
  (* Analyse des instructions du bloc avec la tds du nouveau bloc 
  Cette tds est modifiée par effet de bord *)
   let nli = List.map (analyse_tds_instruction tdsbloc) li in
   (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)
   nli

let  analyse_tds_param tds (typ,nom) =
  match chercherLocalement tds nom with
  | Some _ -> raise (DoubleDeclaration nom)
  | None -> let ia = info_to_info_ast (InfoVar (nom,typ, 0, "") ) in
            ajouter tds nom ia;
            (typ,ia)

(* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds (AstSyntax.Fonction(t,n,lp,li))  =
  match (chercherLocalement maintds n) with
  | Some _ -> raise (DoubleDeclaration n)
  | None -> let info_f = InfoFun (n,t, []) in
            
              let info_f_ast = info_to_info_ast info_f in 
              ajouter maintds n info_f_ast;
              let tdsfille = creerTDSFille maintds in
              let nlp = List.map (analyse_tds_param tdsfille) lp in
              let bli = analyse_tds_bloc tdsfille li in
              Fonction (t, info_f_ast, nlp, bli)

(* analyser : AstSyntax.ast -> AstTds.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (fonctions,prog)) =
  let tds = creerTDSMere () in
  let nf = List.map (analyse_tds_fonction tds) fonctions in 
  let nb = analyse_tds_bloc tds prog in
  Programme (nf,nb)

end
