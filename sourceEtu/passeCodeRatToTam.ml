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
                                              "LOAD ("^(string_of_int (getTaille (get_type ia)))^") "
                                              ^(string_of_int dep)^"["^reg^"]\n"
                                            
                                            else if ((not iOUe) && (not pointeur)) then
                                              "STORE ("^(string_of_int (getTaille t))^") "^(string_of_int dep)^"["^reg^"]\n"
                                            
                                            else if (iOUe && pointeur) then 
                                              "LOAD ("^(string_of_int (getTaille (get_type ia)))^") "
                                              ^(string_of_int dep)^"["^reg^"]\n"^
                                              "LOADI ("^(string_of_int (getTaillePointeur (get_type ia)))^")\n"
                                            
                                            else 
                                              "LOAD ("^(string_of_int (getTaille (get_type ia)))^") "
                                              ^(string_of_int dep)^"["^reg^"]\n"
                                              ^"STOREI ("^string_of_int(getTaillePointeur t)^")\n" (*faux pour le type RAT *)

                            | InfoConst (_,nb) -> "LOADL "^(string_of_int nb)^"\n"
                            | InfoFun _ -> ""
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
                                    (* génére le code pour charger le paramètres dans la pile *)
                                    (List.fold_right (fun x y -> (analyser_tam_expression x)^"\n"^y) b "")
                                    (* Appelle de la fonction *)
                                    ^"CALL (SB) "^nom^"\n"
    | Booleen (bool) -> if bool then "LOADL 1\n" else "LOADL 0\n" (* en code tam bool = (0|1) *)
    | Entier (ent) -> "LOADL "^(string_of_int ent)^"\n" (* charge l'entier dans la pile *)
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
                            ^typa^"\n"
        (* ajout pour les pointeurs *)
    | Null -> "0 \n"
    | New t -> "LOADL "^(string_of_int (getTaille t))^"\n" 
              ^"SUBR MAlloc \n"
    | Affectable (a,_) -> (analyser_tam_affectable a true false)
    | Adresse ia -> let (dep,reg) = (get_dep_reg ia) in
                    "LOADA "^(string_of_int dep)^"["^reg^"]\n"

                        
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
  ^(analyser_tam_expression e)
  ^"STORE ("^(string_of_int taille)^") "^(string_of_int dep)^"["^reg^"]\n"


    | Affectation (a, e) -> (analyser_tam_expression e)^"\n"^(analyser_tam_affectable a false false)
    | AffichageInt e -> (analyser_tam_expression e)^"\n"^"SUBR IOut\n"
    | AffichageRat e -> (analyser_tam_expression e)^"\n"^"CALL (SB) ROut\n"
    | AffichageBool e -> (analyser_tam_expression e)^"\n"^"SUBR Bout\n"
    | Conditionnelle (e,bt,be) -> let etiquetElse = (getEtiquette ()) in
                                  let etiquetFin = (getEtiquette ()) in
                                  (analyser_tam_expression e)^"\n"^"JUMPIF (0) "^etiquetElse^"\n"
                                  ^(analyser_tam_bloc bt ttr tparam)
                                  ^"JUMP "^etiquetFin^"\n"
                                  ^etiquetElse^"\n"
                                  ^(analyser_tam_bloc be ttr tparam)
                                  ^etiquetFin^"\n"
    | TantQue (e,b) -> let etiquetWhile = (getEtiquette ()) in
                        let etiquetFin = (getEtiquette ()) in
                        etiquetWhile^"\n"
                        ^(analyser_tam_expression e)^"\n"
                        ^"JUMPIF (0) "^etiquetFin^"\n"
                        ^(analyser_tam_bloc b ttr tparam)^"\n"
                        ^"JUMP "^etiquetWhile^"\n"
                        ^etiquetFin^"\n"
    | Retour e -> (analyser_tam_expression e)^"\n"
                  ^"RETURN ("^(string_of_int ttr)^") "^(string_of_int tparam)^"\n"
    | Empty -> ""


        
  (* analyse_tam_bloc : AstType.instruction list -> typ -> typ list -> string     *)
  (* Paramètre i : l'instruction à générer le code                                *)
  (* Paramètre ttr : taille du type retour 
        obligatoire lors de l'instruction Return de la fonction                   *)
  (* Paramètre tparam : taille des types des paramètres
        obligatoire lors de l'instruction Return de la fonction                   *)
  (* Génère le code du bloc                                                       *)
  and analyser_tam_bloc li ttr tparam =
  let (bloc_tam, tp) = (List.fold_right (fun x (y,w) -> (analyse_tam_instruction x ttr tparam)^y,(taille_variables x) + w) li ("",0)) in
  bloc_tam
  ^"POP (0) "
  ^(string_of_int (tp))
  ^"\n"


  (* analyser_tam_fonction : AstType.Fonction -> string          *)
  (* Paramètre Fontion(ia,_,b) : Fonction dont on génère le code *)
  (* Génère le code de la fonction                               *)
  let analyser_tam_fonction (Fonction(ia,_,b))  = 
    match (info_ast_to_info ia) with
    | InfoFun (nf, tf, lpf) -> let tparams = (List.fold_right (fun x y -> (getTaille x) + y) lpf 0) in
                              nf^"\n"
                              ^(analyser_tam_bloc b (getTaille tf) tparams)^"\n"
                              ^"HALT\n"
    | _ -> raise (InfoInattendu "InfoFun")


  (* analyser : AstPlacement.Programme -> string                   *)
  (* Paramètre Programme (lf,b) : Programme dont on génère le code *)
  (* Génère le code du programme                                   *)
  let analyser (Programme (lf,b)) =
    ""^(getEntete ())^(String.concat "\n\n" (List.map analyser_tam_fonction lf))^
  "main\n"^
  (analyser_tam_bloc b 0 0)^
  "HALT\n"

end
