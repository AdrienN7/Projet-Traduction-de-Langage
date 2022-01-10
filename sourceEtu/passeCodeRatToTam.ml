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
  
  
  (* get_type : Tds.info_ast -> typ                  *)
  (* Paramètre ia : l'info ast de la variable        *)
  (* renvoie le typ de la variable                   *)
  (* Erreur si mauvaise utilisation des identifiants *)
  let get_type ia =  
    match (info_ast_to_info ia) with
    | InfoVar (_,t,_,_) -> t
    | _ -> raise (InfoInattendu "Infovar")

  (* taille_variables : AstType.instruction -> int                                   *)
  (* Paramètre i : intruction dont on veut connaitre si des variables sont déclarées *)
  (* Renvoie la taille du type de la variable si c'est une déclaration de variable   *)
  let taille_variables i = 
    match i with
    | AstType.Declaration (n, _) -> (getTaille (get_type n))
    | _ -> 0

  (* get_dep_reg : Tds.info_ast -> (int * string)                           *)
  (* Paramètre ia : variable dont on veut connaitre le placement en mémoire *)
  (* Renvoie le placement en mémoire de la variable                         *)
  (* Erreur si ce n'est pas des variables                                   *)
  let get_dep_reg ia =
    match (info_ast_to_info ia) with
    | InfoVar (_,_,dep,reg) -> (dep,reg)
    | _ -> raise (InfoInattendu "Infovar")

  (* getTaillePointeur : typ -> int                                 *)
  (* Paramètre t : type du pointeur                                 *)
  (* Renvoie la taille de la case en mémoire occupé par le pointeur *)
  let rec getTaillePointeur t = 
    match t with 
    | Pointeur t1 -> getTaillePointeur t1
    | _ -> getTaille t


  (* analyser_tam_affection : AstType.affectable -> bool -> bool -> string                   *)
  (* Paramètre a : affectable dont on doit générer le code                                   *)
  (* Paramètre iOUe : permet de savoir si l'affectable est du coté instruction ou expression *)
  (* Paramètre pointeur : permet de sovoir si l'affectable est un pointeur                   *)
  (* Génère le code de l'affectable                                                          *)
  let rec analyser_tam_affectable a iOUe pointeur =
    match a with
      (* si c'est un pointeur, passage du paramètre pointeur à true *)
      | AstType.Deref a1 -> (analyser_tam_affectable a1 iOUe true)

      | AstType.Ident ia -> begin 
                            match (info_ast_to_info ia) with
                            | InfoVar (_,t,dep,reg) -> 

                                            if (iOUe && (not pointeur)) then
                                            (* affectable côté droit de l'affectation et n'est pas un pointeur *)
                                              "LOAD ("^(string_of_int (getTaille (get_type ia)))^") "
                                              ^(string_of_int dep)^"["^reg^"]\n"
                                            
                                            else if ((not iOUe) && (not pointeur)) then
                                            (* affectable coté gauche lors de l'affectation et n'est pas un pointeur *)
                                              "STORE ("^(string_of_int (getTaille t))^") "^(string_of_int dep)^"["^reg^"]\n"
                                            
                                            else if (iOUe && pointeur) then 
                                            (* pointeur coté droit lors de l'affectation *)
                                              "LOAD ("^(string_of_int (getTaille (get_type ia)))^") "
                                              ^(string_of_int dep)^"["^reg^"]\n"^
                                              (* chargement dans la pile de l'adresse du pointeur *)
                                              "LOADI ("^(string_of_int (getTaillePointeur (get_type ia)))^")\n"
                                              (* chargement dans la pile de la case à l'adresse du pointeur *)
                                            
                                            else 
                                            (* pointeur côté gaucche lors de l'affectation *)
                                              "LOAD ("^(string_of_int (getTaille (get_type ia)))^") "
                                              ^(string_of_int dep)^"["^reg^"]\n"
                                              (* chargement dans la pile de l'adresse du pointeur *)
                                              ^"STOREI ("^string_of_int(getTaillePointeur t)^")\n"
                                              (* stockage dans la case mémoire à l'adresse du pointeur *)

                            | InfoConst (_,nb) -> "LOADL "^(string_of_int nb)^"\n" (* si l'affectable est une constante alors forcément coté droit de l'affectation *)
                            | InfoFun _ -> ""  (* cas impossible *)
                            end

  (* analyse_tam_expression : AstType.expression -> string *)
  (* Paramètre e : l'expression à générer le code          *)
  (* Génère le code de l'expression                        *)
  (* Erreur si mauvaise utilisation des Info               *)
  and analyser_tam_expression e =
    match e with
    | AstType.AppelFonction (n,b) -> (* on récupère le nom de la fonction *)
                                    let nom = begin 
                                              match info_ast_to_info n with
                                              | InfoFun(nf, _, _) -> nf
                                              | _ -> raise (InfoInattendu "infoVar") (* erreur impossible car déjà vérifié dans gestion des identifiants *)
                                              end in
                                    (List.fold_right (fun x y -> (analyser_tam_expression x)^"\n"^y) b "")
                                    (* génére le code pour charger le paramètres dans la pile *)
                                    ^"CALL (SB) "^nom^"\n"
                                    (* Appelle de la fonction *)

    | Booleen (bool) -> if bool then "LOADL 1\n" else "LOADL 0\n" (* en code tam bool = (0|1) *)
    | Entier (ent) -> "LOADL "^(string_of_int ent)^"\n" (* charge l'entier dans la pile *)
    | Unaire (u,exp) -> let typa = begin match u with
                                  | Denominateur -> "POP (1) 1\n" (* on retire de la pile le numérateur *)
                                  | Numerateur -> "POP (0) 1\n" (* on retire de la pile le dénominateur *)
                                    end in
                        (analyser_tam_expression exp)^"\n"
                        ^typa
    | Binaire (b, e1, e2) -> let typa = begin match b with
                              (* les différents calculs sur les binaires *)
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
              (* réservation d'un emplacement mémoire dans le tas de la taille nécessaire au type t*)
    | Affectable (a,_) -> (analyser_tam_affectable a true false)
    | Adresse ia -> let (dep,reg) = (get_dep_reg ia) in
                    "LOADA "^(string_of_int dep)^"["^reg^"]\n"
                    (* charge dans la pile l'emplacement en mémoire de la variable (dans le but de récuperer son adresse)*)

                        
  (* analyse_tam_intruction : AstType.instruction list -> typ -> typ list -> string *)
  (* Paramètre i : l'instruction à générer le code                                  *)
  (* Paramètre ttr : taille du type retour, 
              obligatoire pour le Return de la fonction appelé                      *)
  (* Paramètre tparam : taille des types des paramètres,
              obligatoire pour le Return de la fonction appelé                      *)
  (* Génère le code de l'instruction                                                *)
  let rec analyse_tam_instruction i ttr tparam =
    match i with
    | AstType.Declaration (n, e) -> let taille = (getTaille (get_type n)) in
                                    let (dep,reg) = (get_dep_reg n) in
                                    "PUSH "^(string_of_int taille)^"\n"
                                    (* on push dans le tas de la taille du type *)
                                    ^(analyser_tam_expression e)
                                    ^"STORE ("^(string_of_int taille)^") "^(string_of_int dep)^"["^reg^"]\n"
                                    (* on stocke la valeur de la variable à l'endroit calculé à la passe placement *)

    | Affectation (a, e) -> (analyser_tam_expression e)^"\n"^(analyser_tam_affectable a false false)
                            (* generation du code avec l'affectable à gauche de l'affectation *)
    | AffichageInt e -> (analyser_tam_expression e)^"\n"^"SUBR IOut\n"
    | AffichageRat e -> (analyser_tam_expression e)^"\n"^"CALL (SB) ROut\n"
    | AffichageBool e -> (analyser_tam_expression e)^"\n"^"SUBR Bout\n"
    | Conditionnelle (e,bt,be) -> let etiquetElse = (getEtiquette ()) in
                                  (* cree l'étiquette de début du else *)
                                  let etiquetFin = (getEtiquette ()) in
                                  (* crée l'étiquette de fin de la conditionnelle *)
                                  (analyser_tam_expression e)^"\n"^"JUMPIF (0) "^etiquetElse^"\n"
                                  (* code pour analyser la condition et aller au bloc if ou else *)
                                  ^(analyser_tam_bloc bt ttr tparam)
                                  (* code du bloc if *)
                                  ^"JUMP "^etiquetFin^"\n"
                                  (* aller à la fin de la conditionnelle *)
                                  ^etiquetElse^"\n"
                                  ^(analyser_tam_bloc be ttr tparam)
                                  (* code du bloc else *)
                                  ^etiquetFin^"\n"
    | TantQue (e,b) -> let etiquetWhile = (getEtiquette ()) in
                        let etiquetFin = (getEtiquette ()) in
                        etiquetWhile^"\n"
                        ^(analyser_tam_expression e)^"\n"
                        (* code pour analyser la condition *)
                        ^"JUMPIF (0) "^etiquetFin^"\n"
                        (* si la condition est pas remplit go à la fin du while *)
                        ^(analyser_tam_bloc b ttr tparam)^"\n"
                        (* bloc du while *)
                        ^"JUMP "^etiquetWhile^"\n"
                        (* retour au début du while *)
                        ^etiquetFin^"\n"
    | Retour e -> (analyser_tam_expression e)^"\n"
                  ^"RETURN ("^(string_of_int ttr)^") "^(string_of_int tparam)^"\n"
                  (* retour de la fonction avec la taille du type retour et la taille des paramètres appelés *)
    | Empty -> ""

    | Addition (a,e) -> (analyser_tam_expression e)^"\n"^(analyser_tam_affectable a false false)


        
  (* analyse_tam_bloc : AstType.instruction list -> typ -> typ list -> string     *)
  (* Paramètre i : l'instruction à générer le code                                *)
  (* Paramètre ttr : taille du type retour 
        obligatoire lors de l'instruction Return de la fonction                   *)
  (* Paramètre tparam : taille des types des paramètres
        obligatoire lors de l'instruction Return de la fonction                   *)
  (* Génère le code du bloc                                                       *)
  and analyser_tam_bloc li ttr tparam =
  let (bloc_tam, tp) = (List.fold_right (fun x (y,w) -> (analyse_tam_instruction x ttr tparam)^y,(taille_variables x) + w) li ("",0)) in
  (* génération du code du bloc et calcul de la taille des types des varaibles locales *)
  bloc_tam
  ^"POP (0) "
  ^(string_of_int (tp)) (* retrait dans la pile des variables locales *)
  ^"\n"


  (* analyser_tam_fonction : AstType.Fonction -> string          *)
  (* Paramètre Fontion(ia,_,b) : Fonction dont on génère le code *)
  (* Génère le code de la fonction                               *)
  let analyser_tam_fonction (Fonction(ia,_,b))  = 
    match (info_ast_to_info ia) with
    | InfoFun (nf, tf, lpf) -> let tparams = (List.fold_right (fun x y -> (getTaille x) + y) lpf 0) in
                              (* calcul de la taille totale des paramètres d'entrée *)
                              nf^"\n" (* nom de la fonction *)
                              ^(analyser_tam_bloc b (getTaille tf) tparams)^"\n" 
                              (* génération du code du bloc de la fonction avec taille type retour et paramètres*)
                              ^"HALT\n" (* fin de la fonction essentiel si oublie de l'instruction return *)
    | _ -> raise (InfoInattendu "InfoFun") (* Erreur impossible *)


  (* analyser : AstPlacement.Programme -> string                   *)
  (* Paramètre Programme (lf,b) : Programme dont on génère le code *)
  (* Génère le code du programme                                   *)
  let analyser (Programme (lf,b)) =
    ""^(getEntete ())^(String.concat "\n\n" (List.map analyser_tam_fonction lf))^
    (* place au début du code du programme l'en-tête contenant différents programmes basiques *)
    (* puis le code des différentes fonctions implantées dans le programme *)
  "main\n"^
  (* début du code main *)
  (analyser_tam_bloc b 0 0)^
  (* génération du code du bloc principal donc pas de type retour et pas de paramètre *)
  "HALT\n"

end
