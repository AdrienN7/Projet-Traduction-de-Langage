(* Module de la passe de gestion des identifiants *)
module PasseTdsRat : Passe.Passe with type t1 = Ast.AstSyntax.programme and type t2 = Ast.AstTds.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstTds

  type t1 = Ast.AstSyntax.programme
  type t2 = Ast.AstTds.programme
  
  (* trouverIa : affectable -> info_ast  *)
  (* Paramètre iaa1 : affectable         *)
  (* Retourne l'info_ast de l'affectable *)
  let rec trouverIa iaa1 =
    match iaa1 with
    | Deref(a1) -> trouverIa a1
    | Ident(ia) -> ia
    | Acces _ -> failwith ("Impossible")

  (* trouvern : string -> info_ast list -> info_ast                  *)
  (* Paramètre n : le nom du champ recherché                         *)
  (* Paramètre lia : la liste des ast présente dans l'enregistrement *)
  (* Retourne l'ia de du champ recherché dans l'enregistrement       *)
  (* Erreur si il n'est pas présent dans l'enregistrement            *)
  let rec trouvern n lia =
    match lia with 
    | [] -> raise (MauvaiseUtilisationIdentifiant n) 
    | ia::q -> let info = info_ast_to_info ia in
               begin match info with
                  | InfoVar(n1,_,_,_) -> if (n = n1) then ia else (trouvern n q)
                  | InfoConst (n1,_) -> raise (MauvaiseUtilisationIdentifiant n1)
                  (* les enregistrements n'ont pas de champ constant *)
                  | InfoTyp (n1,_) -> raise (MauvaiseUtilisationIdentifiant n1)
                  | InfoFun (n1,_,_) -> raise (MauvaiseUtilisationIdentifiant n1)
                  | InfoRecord (n1,_) -> if (n1 = n) then ia else (trouvern n q)
               end

  (* trouverIAdeN : string -> affectable -> info_ast                  *)
  (* Paramètre n : nom du champ recherché                             *)
  (* Paramètre iaa1 : affectable où on cherche le champs              *)
  (* Retourne l'info_ast correspondant à n dans l'affectable iaa1     *)
  (* Erreur si l'affectable n'est pas un record ou pointeur de record *)
  (* Erreur si n n'est pas défini dans l'enregistrement               *)
  let trouverIAdeN n iaa1 =
    let ia = trouverIa iaa1 in
    let info = info_ast_to_info ia in
    match info with
    | InfoRecord (_,lia) -> let ian = (trouvern n lia) in
                              ian
    | InfoConst (n1,_) -> raise (MauvaiseUtilisationIdentifiant n1) 
    | InfoVar (n1,_,_,_) -> raise (MauvaiseUtilisationIdentifiant n1)
    | InfoTyp (n1,_) -> raise (MauvaiseUtilisationIdentifiant n1)
    | InfoFun (n1,_,_) -> raise (MauvaiseUtilisationIdentifiant n1)

  (* analyse_tds_record : tds -> typ * string -> info_Ast                                       *)
  (* Paramètre tds : la tds du programme                                                        *)
  (* Paramètre (t,n) : un des champ défini dans la structure Record                             *)
  (* Retourne l'ast_info de ce champ après avoir vérifié qu'il n'est pas déjà défini localement *)
  (* Erreur si double décaration                                                                *)
  let analyse_tds_record tds (t,n)=
    match (chercherLocalement tds n) with
    | Some _ -> raise (DoubleDeclaration n)
    | None -> let info = InfoVar (n, t, 0, "") in 
              let ia = info_to_info_ast info in
              ajouter tds n ia;
              ia

  (* analyse_tds_td : tds -> AstSyntax.nommes -> nommes              *)
  (* Paramètre tds : tds du programme                                *)
  (* Paramètre tn : type nommé à ajouter à la tds                    *)
  (* renvoie nommé après avoir vérifié qu'il n'était pas déjà defini *)
  (* Erreur si double déclaraton                                     *)
  let  analyse_tds_td tds tn = 
    match tn with
    | AstSyntax.Typedefglobal (n,t) -> begin
                              match (chercherGlobalement tds n) with
                              | Some _ -> raise (DoubleDeclaration n)
                              | None ->  let info_t = InfoTyp (n,t) in
                                let ia = info_to_info_ast info_t in
                                ajouter tds n ia;
                                Typedefglobal (n,t)
                            end

  (* analyse_tds_affectable : AstSyntax.affectable -> AstTds.affectable *)
  (* Paramètre tds : la table des symboles courante *)
  (* Paramètre a : l'affectable à analyser *)
  (* Paramètre modif : boolen qui permet de savoir si la constant est modifié ou pas *)
  (* Vérifie la bonne utilisation des identifiants et tranforme l'affectable
  en une afectable de type AstTds.affectable *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let rec analyse_tds_affectable tds modif a =
    match a with
   (* Deref: analyse de l'affectable pointé *)
   | AstSyntax.Deref a1 -> Deref(analyse_tds_affectable tds modif a1)
   (* Ident : verifie l'existance de l'id et de se bonne utilisation*)
   | AstSyntax.Ident n -> 
   begin
        match (chercherGlobalement tds n) with
        | None ->  raise (IdentifiantNonDeclare n)
        | Some ia -> 
          begin  
            match (info_ast_to_info ia) with
            (* Si c'est une contente et qu'elle est modifié on cri *)
            | InfoConst (n,_) -> if modif then raise (MauvaiseUtilisationIdentifiant n)
                                 else Ident(ia)
            | InfoVar _ -> Ident(ia)
            | InfoRecord _ -> Ident(ia)
            | _ -> raise (MauvaiseUtilisationIdentifiant n)
          end
    end
  | AstSyntax.Acces (a1,n) -> 
  begin
      match (chercherLocalement tds n) with
        | Some _ ->  raise (DoubleDeclaration n)
        | None -> 
                    let iaa1 = (analyse_tds_affectable tds modif a1) in
                    let ia = (trouverIAdeN n iaa1) in
                    Acces(iaa1,ia)
  end

(* analyse_tds_expression : AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)

let rec analyse_tds_expression tds e =
  match e with
  (* AppelFonction: verifie l'existance de l'id  *)
  | AstSyntax.AppelFonction (n, li) -> 
    begin
      match (chercherGlobalement tds n) with 
         | None -> raise (IdentifiantNonDeclare n)
         | Some ia -> begin
                      (* verifie que c'est bien une infofun et renvoie appelfonction avec info_ast et l'analyse des parametres*)
                      match info_ast_to_info ia with
                      | InfoFun(_) -> AppelFonction (ia,(List.map (analyse_tds_expression tds) li))
                      | _ -> raise (MauvaiseUtilisationIdentifiant n)
         end
    end
   (*Affectable: renvoie affectable avec l'analyse de son contenu *)
  | AstSyntax.Affectable a1 -> Affectable(analyse_tds_affectable tds false a1)  
  | AstSyntax.Null -> Null 
  | AstSyntax.New t -> New (t)
  (*Adresse: vérifie l'existance de l'id et renvoie l'info_ast si c'est bien une infovar  *)
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
  (*Booleen et entier: renvoie la meme strucutre car pas d'id  *)
  | AstSyntax.Booleen n -> Booleen (n)
  | AstSyntax.Entier n -> Entier (n)
  (*Unaire et binaire renvoie la même structure avec l'annalyse de leur expression *)
  | AstSyntax.Unaire (u, e1) -> Unaire (u, (analyse_tds_expression tds e1))
  | AstSyntax.Binaire (b, e1, e2) -> Binaire (b, analyse_tds_expression tds e1, analyse_tds_expression tds e2)
  | AstSyntax.Enregistrement l -> Enregistrement (List.map(analyse_tds_expression tds) l)


  
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
            let  info = 
            begin
            match t with 
            | Record lt -> let lia = List.map (analyse_tds_record tds) lt in
                           InfoRecord (n,lia)
                           
            | _ ->
              (* Création de l'information associée à l'identfiant *)
              InfoVar (n,t, 0, "") 
            end in
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
      (*Analyse de l'expression*)
      let ne = analyse_tds_expression tds e in
      (*Analyse de l'affectable *)
      let na = analyse_tds_affectable tds true a in
      Affectation(na, ne)
    
    (* ajout pour l'operateur d'assignation *)
  | AstSyntax.Addition (a1,e1) -> 
      (*Analyse de l'expression*)
      let ne = analyse_tds_expression tds e1 in
      (*Analyse de l'affectable *)
      let na = analyse_tds_affectable tds true a1 in
      Addition(na, ne)

  (* définition local d'un type nommé *)
  | AstSyntax.Typedeflocal (n,t) -> begin
                              match (chercherLocalement tds n) with
                              (* Vérifie s'il n'est pas déja nommé localement *)
                              | Some _ -> raise (DoubleDeclaration n)
                              | None ->  let info_t = InfoTyp (n,t) in
                                let ia = info_to_info_ast info_t in
                                (* Créé l'infotyp l'ajoute à la tds *)
                                ajouter tds n ia;
                                (* renvoie l'instructuion avec l'info_ast *)
                                Typedeflocal (n,t)
                            end

      
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


(* analyse_tds_param : Tds.tds -> (Type.typ * String) -> (Type.typ * info_ast) *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre (Type.typ * String) : paramètre a ajouter *)
(* Vérifie la bonne utilisation des identifiants et ajoute le parametre dans la tds *)
(* Erreur si mauvaise utilisation des identifiants *)
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
  (*Cherche localement l'id pour verifié qu'elle n'existe pas déja *)
  match (chercherLocalement maintds n) with

  | Some _ -> raise (DoubleDeclaration n)
  (*Créé l'infofun pour la fonction  *)
  | None -> let info_f = InfoFun (n,t, []) in
              (*ajoute l'infofun à la tds *)
              let info_f_ast = info_to_info_ast info_f in 
              ajouter maintds n info_f_ast;
              (* Créé la tds fille  analyse les paramètre et le bloc de la fonction*)
              let tdsfille = creerTDSFille maintds in
              let nlp = List.map (analyse_tds_param tdsfille) lp in
              let bli = analyse_tds_bloc tdsfille li in
              (* renvoie la fonction avec type de retour - informations associées à l'identificateur (dont son nom) - liste des paramètres (association type et information sur les paramètres) - corps de la fonction *)
              Fonction (t, info_f_ast, nlp, bli)

(* analyser : AstSyntax.ast -> AstTds.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (tnl,fonctions,prog)) =
  (*creer la tds mere *)
  let tds = creerTDSMere () in
  (*analyse les fonction du programme *)
  let nf = List.map (analyse_tds_fonction tds) fonctions in 
  (*analyse le bloc du programme *)
  let nb = analyse_tds_bloc tds prog in
  (*analyse les types nommé globalement *)
  let ntdl = List.map (analyse_tds_td tds) tnl in
  (* Renvoie la Structure d'un programme dans notre langage *)
  Programme (ntdl,nf,nb)

end
