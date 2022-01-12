/* Imports. */

%{

open Type
open Ast.AstSyntax
%}


%token <int> ENTIER
%token <string> ID
%token RETURN
%token PV
%token AO
%token AF
%token PF
%token PO
%token EQUAL
%token CONST
%token PRINT
%token IF
%token ELSE
%token WHILE
%token BOOL
%token INT
%token RAT
%token CALL 
%token CO
%token CF
%token SLASH
%token NUM
%token DENOM
%token TRUE
%token FALSE
%token PLUS
%token MULT
%token INF
%token EOF

(* ajout des pointeurs *)
%token ET
%token NEW
%token NULL

(*ajout pour les types nommés*)
%token TYPEDEF
%token <string> TID

(*ajout pour les enregistrements *)
%token STRUCT
%token PT

(* Type de l'attribut synthétisé des non-terminaux *)
%type <programme> prog
%type <nommes list> td
%type <instruction list> bloc
%type <fonction> fonc
%type <instruction list> is
%type <instruction> i
%type <typ> typ
%type <(typ*string) list> dp
%type <expression> e 
%type <expression list> cp
%type <affectable> a (* ajout de l'affectable *)


(* Type et définition de l'axiome *)
%start <Ast.AstSyntax.programme> main

%%

main : lfi = prog EOF     {lfi}

prog :
| td1 = td  lf = fonc  lfi = prog   {let (Programme (ltd,lf1,li))=lfi in (Programme (td1@ltd,lf::lf1,li))}
| ID li = bloc            {Programme ([],[],li)}

td :
|                         {[]}
| TYPEDEF tn=TID EQUAL t=typ PV td1=td {(Typedefglobal (tn,t))::td1}

fonc : t=typ n=ID PO p=dp PF AO li=is AF {Fonction(t,n,p,li)}

bloc : AO li = is AF      {li}

is :
|                         {[]}
| i1=i li=is              {i1::li}

i :
| t=typ n=ID EQUAL e1=e PV          {Declaration (t,n,e1)}
| a1 = a EQUAL e1=e PV              {Affectation (a1,e1)}
| CONST n=ID EQUAL e=ENTIER PV      {Constante (n,e)}
| PRINT e1=e PV                     {Affichage (e1)}
| IF exp=e li1=bloc ELSE li2=bloc   {Conditionnelle (exp,li1,li2)}
| WHILE exp=e li=bloc               {TantQue (exp,li)}
| RETURN exp=e PV                   {Retour (exp)}
| a1=a PLUS EQUAL e1=e PV           {Addition (a1,e1)} (*Ajout d'une instruction pour l'operateur d'assignation Addition*)
| TYPEDEF tn=TID EQUAL t=typ PV     {Typedeflocal (tn,t)} (* définition locale d'un type nommé *)

a : (*implentation de l'affectable*)
| n=ID       {Ident (n)} 
| PO MULT a1=a PF {Deref (a1)} 
| PO a1=a PT n=ID PF {Acces(a1,n)}

dp :
|                         {[]}
| t=typ n=ID lp=dp        {(t,n)::lp}

typ :
| BOOL    {Bool}
| INT     {Int}
| RAT     {Rat}
| t=typ MULT {Pointeur (t)} (* Ajout du typ pointeurs*)
| tn=TID   {Tident (tn)}        (*utilisation d'un type nommé*)
| STRUCT AO d=dp AF {Record (d)}       (*ajout du type enregistrement*)


e : 
| CALL n=ID PO lp=cp PF   {AppelFonction (n,lp)}
| CO e1=e SLASH e2=e CF   {Binaire(Fraction,e1,e2)}
(* n=ID                    {Ident n}*) (*on supprime l'expression identifiant*)
| TRUE                    {Booleen true}
| FALSE                   {Booleen false}
| e=ENTIER                {Entier e}
| NUM e1=e                {Unaire(Numerateur,e1)}
| DENOM e1=e              {Unaire(Denominateur,e1)}
| PO e1=e PLUS e2=e PF    {Binaire (Plus,e1,e2)}
| PO e1=e MULT e2=e PF    {Binaire (Mult,e1,e2)}
| PO e1=e EQUAL e2=e PF   {Binaire (Equ,e1,e2)}
| PO e1=e INF e2=e PF     {Binaire (Inf,e1,e2)}
| PO exp=e PF             {exp}
| a1=a                   {Affectable (a1)}  (* ajout des différentes expression pour le pointeur*)
| NULL                    {Null}  
| PO NEW t=typ PF         {New (t)}    
| ET n=ID                 {Adresse (n)} 
| AO cp1=cp AF            {Enregistrement (cp1)}




cp :
|               {[]}
| e1=e le=cp    {e1::le}

