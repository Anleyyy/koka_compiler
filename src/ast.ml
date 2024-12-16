type loc = Lexing.position * Lexing.position
type ident = string

exception CError of string
exception GlobalError of string
exception Error of loc * string

type binop =
  | Badd | Bsub | Bmul | Bdiv | Bmod    (* + - * / % *)
  | Beq | Bneq | Blt | Ble | Bgt | Bge  (* == != < <= > >= *)
  | Bconcat | Band | Bor                (* ++ && ||*)

type file = decl list

and decl = ident * funbody * loc

and funbody = param list * annot * expr

and param = ident * kokatype

and annot = 
  | Noannot
  | Annot of result

and result = ident list * kokatype

and kokatype = 
  | Katype of akokatype
  | Kmonoparam of akokatype * result
  | Kpluriparam of kokatype list * result

and akokatype =
  | Aknoparam of ident
  | Akparam of ident * kokatype
  | Akbracket of kokatype
  | Akunit

and atom = {a_content : catom; loc : loc}

and catom =
  | Aunit
  | Abool of bool
  | Astring of string
  | Aint of int
  | Aident of ident
  | Aexpr of expr
  | Acall of atom * expr list
  | Alist of expr list

and expr = {content : cexpr; loc : loc}

and cexpr = 
  | Eblock of block
  | Ebexpr of bexpr

and bexpr = {b_content : cbexpr; loc : loc}

and cbexpr = 
  | Batom of atom
  | Bneg of bexpr
  | Bnot of bexpr
  | Bbinop of binop * bexpr * bexpr
  | Bassign of ident * bexpr
  | Bif of bexpr * expr * expr
  | Bfn of funbody
  | Breturn of expr

and block = stmt list

and stmt = 
  | Sbexpr of bexpr
  | Sval of ident * expr
  | Svar of ident * expr

let binop_to_string = function
  | Badd -> "+"
  | Bsub -> "-"
  | Bmul -> "*"
  | Bdiv -> "/"
  | Bmod -> "%"
  | Beq -> "=="
  | Bneq -> "!="
  | Blt -> "<"
  | Ble -> "<="
  | Bgt -> ">"
  | Bge -> ">="
  | Bconcat -> "++"
  | Band -> "&&"
  | Bor -> "||"



let loc_to_string (start_pos, end_pos) =
  let start_line = start_pos.Lexing.pos_lnum in
  let start_col = start_pos.Lexing.pos_cnum - start_pos.Lexing.pos_bol + 1 in
  let end_line = end_pos.Lexing.pos_lnum in
  let end_col = end_pos.Lexing.pos_cnum - end_pos.Lexing.pos_bol + 1 in
  "(" ^ string_of_int start_line ^ ":" ^ string_of_int start_col ^ "-" ^
  string_of_int end_line ^ ":" ^ string_of_int end_col ^ ")"

let rec atom_to_string {a_content; loc} =
  let loc_str = loc_to_string loc in
  match a_content with
  | Aunit -> "unit" ^ loc_str
  | Abool b -> string_of_bool b ^ loc_str
  | Astring s -> "\"" ^ s ^ "\"" ^ loc_str
  | Aint i -> string_of_int i ^ loc_str
  | Aident id -> id ^ loc_str
  | Aexpr e -> "expr(" ^ expr_to_string e ^ ")" ^ loc_str
  | Acall (a, args) ->
    "call(" ^ atom_to_string a ^ ", [" ^ 
    String.concat ", " (List.map expr_to_string args) ^ "])" ^ loc_str
  | Alist lst ->
    "list([" ^ String.concat ", " (List.map expr_to_string lst) ^ "])" ^ loc_str
  
and catom_to_string content =
  match content with
  | Aunit -> "unit"
  | Abool b -> string_of_bool b 
  | Astring s -> "\"" ^ s ^ "\"" 
  | Aint i -> string_of_int i 
  | Aident id -> id 
  | Aexpr e -> "expr(" ^ expr_to_string e ^ ")" 
  | Acall (a, args) ->
    "call(" ^ atom_to_string a ^ ", [" ^ 
    String.concat ", " (List.map expr_to_string args) ^ "])" 
  | Alist lst ->
    "list([" ^ String.concat ", " (List.map expr_to_string lst) ^ "])" 

and expr_to_string {content; loc} =
  let loc_str = loc_to_string loc in
  match content with
  | Eblock b -> "block(" ^ block_to_string b ^ ")" ^ loc_str
  | Ebexpr b -> "bexpr(" ^ bexpr_to_string b ^ ")" ^ loc_str

and block_to_string stmts = 
  "[" ^ String.concat "; " (List.map stmt_to_string stmts) ^ "]"

and stmt_to_string = function
  | Sbexpr b -> "bexpr(" ^ bexpr_to_string b ^ ")"
  | Sval (id, e) -> id ^ " = " ^ expr_to_string e
  | Svar (id, e) -> "var " ^ id ^ " = " ^ expr_to_string e

and bexpr_to_string {b_content; loc} =
  let loc_str = loc_to_string loc in
  match b_content with
  | Batom a -> "atom(" ^ atom_to_string a ^ ")" ^ loc_str
  | Bneg b -> "neg(" ^ bexpr_to_string b ^ ")" ^ loc_str
  | Bnot b -> "not(" ^ bexpr_to_string b ^ ")" ^ loc_str
  | Bbinop (op, b1, b2) ->
    "binop(" ^ binop_to_string op ^ ", " ^ 
    bexpr_to_string b1 ^ ", " ^ bexpr_to_string b2 ^ ")" ^ loc_str
  | Bassign (id, b) -> "assign(" ^ id ^ ", " ^ bexpr_to_string b ^ ")" ^ loc_str
  | Bif (cond, e1, e2) ->
    "if(" ^ bexpr_to_string cond ^ ", " ^ expr_to_string e1 ^ ", " ^ expr_to_string e2 ^ ")" ^ loc_str
  | Bfn f -> "fn(" ^ funbody_to_string f ^ ")" ^ loc_str
  | Breturn e -> "return(" ^ expr_to_string e ^ ")" ^ loc_str

and funbody_to_string (params, annot, e) =
  "[" ^ String.concat ", " (List.map (fun (id, _) -> id) params) ^ "] -> " ^ 
  annot_to_string annot ^ " : " ^ expr_to_string e

and annot_to_string = function
  | Noannot -> "Noannot"
  | Annot (ids, _) -> "Annot(" ^ String.concat ", " ids ^ ")"

let rec file_to_string (f : file) =
  "File with declarations:\n" ^ 
  String.concat "\n" (List.map decl_to_string f)

and decl_to_string (id, funbody,loc) =
  "Function " ^ id ^ " -> " ^ funbody_to_string funbody ^ (loc_to_string loc)
