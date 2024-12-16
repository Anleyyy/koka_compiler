
/* Analyseur syntaxique pour mini-koka */

%{
  open Ast

let rec handle_elif bel e =
match bel with
| (b0, e0)::[] -> Bif (b0, e0, e)
| (b0, e0)::s -> Bif (b0, e0, 
    {content = Ebexpr {b_content = (handle_elif s e); loc = e.loc}; loc = e.loc})
| [] -> failwith "Impossible case"
%}

/* Déclaration des tokens */

%token <Ast.catom> ATM
%token <Ast.binop> CMP
%token LT GT
%token <string> IDENT
%token IF ELSE ELIF RETURN FUN FN THEN VAL VAR
%token EOF
%token LP RP LSQ RSQ LBRACE RBRACE COMMA DOT COLON SCOLON 
%token EQUAL ASSIGN NEGATE NOT ARROW
%token CONCAT AND OR
%token PLUS MINUS TIMES DIV MOD


/* Priorités et associativités des tokens */

%nonassoc IF
%left OR
%left AND
%nonassoc CMP ASSIGN LT GT
%left PLUS MINUS CONCAT
%left TIMES DIV MOD
%nonassoc NOT NEGATE
%nonassoc ELSE

/* Point d'entrée de la grammaire */
%start file

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <Ast.file> file
%type <Ast.decl> decl
%type <Ast.funbody> funbody
%type <Ast.param> param
%type <Ast.annot> annot
%type <Ast.result> result
%type <Ast.kokatype> kokatype
%type <Ast.akokatype> akokatype
%type <Ast.atom> atom
%type <Ast.catom> catom
%type <Ast.expr> expr
%type <Ast.cexpr> cexpr
%type <Ast.cbexpr> cbexpr
%type <Ast.bexpr> bexpr
%type <Ast.block> block
%type <Ast.stmt> stmt
%type <Ast.ident> ident



%%

/* Règles de grammaire */

file:
  |SCOLON* dl = decl_list SCOLON* EOF /* modification dde separated_list par separated_nonempty_list*/ /*ajout de SCOLON* à la fin */
    { dl }
  |SCOLON* EOF 
    {[]}
;

decl_list:
  | d = decl
      { [d] }
  | d = decl_list SCOLON+ dt = decl
      { d @ [dt] }
;


decl:
  |FUN id = ident fb = funbody
    { (*print_endline ("Parsed decl: " ^ id);*) (id, fb, ($startpos, $endpos)) }
  |FUN id = ident LP separated_list(COMMA, param) RP a = annot
    {raise (CError "syntax error, this function declaration needs an expression")}
  |FUN id = ident 
    {raise (CError "syntaxe error, this function doens't have parameters, ( needed")}
;


funbody:
  LP pl = separated_list(COMMA, param) RP a = annot e = expr
    { (*print_endline "Parsed funbody";*) (pl, a, e) }
;



param:
  id = ident COLON k = kokatype
    { (*print_endline ("Parsed param: " ^ id);*) (id, k) }
;

annot:
| COLON r = result {Annot r}
| {Noannot}
;

result:
| k = kokatype {[], k}
| LT idl = separated_list(COMMA, ident) GT k = kokatype
    {idl, k}
;

kokatype:
| a = akokatype
    {Katype a}
| a = akokatype ARROW r = result
    {Kmonoparam (a, r)}
| LP kl = separated_list(COMMA, kokatype) RP ARROW r = result
    {Kpluriparam (kl, r)}
;

akokatype:
| id = ident 
    {Aknoparam id}
| id = ident LT k = kokatype GT
    {Akparam (id, k)}
| LP k = kokatype RP
    {Akbracket k}
| LP RP
    {Akunit}
;

atom:
    d = catom
    { {a_content = d; loc = $startpos, $endpos} }

catom:
| a = ATM
    {(*print_endline "Parsed atom";*)a}
| LP RP 
    {Aunit}
| id = ident
    {Aident id}
| LP e = expr RP
    {Aexpr e}
| a = atom LP el = separated_list(COMMA, expr) RP
    {Acall (a, el)}
| a = atom DOT id = ident
    {Acall ({a_content = Aident id; loc = $startpos, $endpos}, [{content = Ebexpr {b_content = (Batom a); loc = $startpos, $endpos}; loc = $startpos, $endpos}])}
| a = atom FN fb = funbody
    {match a.a_content with
    | Acall (a', el) -> 
      Acall (a', el @ [{content = Ebexpr {b_content = (Bfn fb); loc = $startpos, $endpos}; loc = $startpos, $endpos}])
    | _ -> Acall (a, [{content = Ebexpr {b_content = (Bfn fb); loc = $startpos, $endpos}; loc = $startpos, $endpos}])}
| a = atom b = block
    {match a.a_content with
    | Acall (a', el) -> 
      Acall (a', el @ [{content = Ebexpr {b_content = (Bfn ([], Noannot, {content = Eblock b;
      loc = $startpos, $endpos})); loc = $startpos, $endpos};
      loc = $startpos, $endpos}])
    | _ -> 
      Acall (a, [{content = Ebexpr {b_content = (Bfn ([], Noannot, {content = Eblock b;
      loc = $startpos, $endpos})); loc = $startpos, $endpos};
      loc = $startpos, $endpos}])}
| LSQ el = separated_list(COMMA, expr) RSQ
    {Alist el}
;

expr:
  c = cexpr
    { {content = c; loc = $startpos, $endpos} }
;

cexpr:
| b = block
    {Eblock b}
| b = bexpr
    {Ebexpr b}
;

bexpr:
  c = cbexpr
  { {b_content = c; loc = $startpos, $endpos} }

cbexpr:
| a = atom
    {Batom a}
| NEGATE b = bexpr
    {Bneg b}
| NOT b = bexpr
    {Bnot b}
| b1 = bexpr b = binop b2 = bexpr
    {Bbinop (b, b1, b2)}
| id = ident ASSIGN b = bexpr
    {Bassign (id, b)}
| IF bel = separated_nonempty_list(ELIF, separated_pair(bexpr, THEN, expr)) ELSE e = expr
    {handle_elif bel e}
| IF bel = separated_nonempty_list(ELIF, separated_pair(bexpr, THEN, expr))
    {handle_elif bel {content = Eblock []; loc = $startpos, $endpos}}
| IF b = bexpr RETURN e = expr
    {Bif (b, {content = Ebexpr ({b_content = Breturn e; loc = $startpos, $endpos}); loc = $startpos, $endpos}, 
        {content = Eblock []; loc = $startpos, $endpos})}
| FN fb = funbody
    {Bfn fb}
| RETURN e = expr
    {Breturn e}
| binop
    {raise (CError "syntax error, a binary operator should separate 2 expressions") }
| NEGATE 
    {raise (CError "syntax error, the operator ~ should precedes an expression")}
| NOT 
    {raise (CError "syntax error, the operator ! should precedes an expression")}
;



block:
  | LBRACE SCOLON* s = stmt_list SCOLON* RBRACE
      { let rec test_var_val l = (match l with
      |[] -> failwith "Houston we've got a problem"
      |[t] -> (match t with |Sbexpr a -> [t] |_ -> raise (CError "syntax error, a statement can't be ended by a declaration"))
      |t::q -> t::(test_var_val q)) in
        (*print_endline ("Parsed block with " ^ string_of_int (List.length s) ^ " statements");*) test_var_val s }
  | LBRACE SCOLON* RBRACE
      { (*print_endline "Parsed empty block";*) [] }
;

stmt_list:
  | st = stmt
      {[st] }
  | s = stmt_list SCOLON+ st = stmt
      {s @ [st] }
  | stmt stmt
      {raise (CError "syntax error, 2 statements must me separated by a semi colon")}
  | stmt_list SCOLON+ stmt stmt
      {raise (CError "syntax error, 2 statements must me separated by a semi colon")}
;




stmt:
| b = bexpr
    {Sbexpr b}
| VAL id = ident EQUAL e = expr
    {Sval (id, e)}
| VAR id = ident ASSIGN e = expr
    {Svar (id, e)}
;

%inline binop:
| PLUS  { Badd }
| MINUS { Bsub }
| TIMES { Bmul }
| DIV   { Bdiv }
| MOD   { Bmod }
| c=CMP { c    }
| LT    { Blt  }
| GT    { Bgt  }
| CONCAT{ Bconcat}
| AND   { Band }
| OR    { Bor  }
;

ident:
  id = IDENT
    { id }
;
