open Ast

type calctype = effect * valtype

and valtype = 
  | Vweak
  | Vunit
  | Vbool
  | Vint 
  | Vstring
  | Vlist of valtype
  | Vmaybe of valtype
  | Varrow of valtype list * calctype

and effect = 
  | Enone
  | Ediv
  | Econsole
  | Eall

type weakval = int

type ucalctype = ueffect * uvaltype 

and uvaltype =
  | Mutable of weakval
  | Fixed of valtype
  | Ulist of uvaltype
  | Umaybe of uvaltype
  | Uarrow of uvaltype list * ucalctype

and ueffect = 
  | Efixed of effect 
  | Emutable of effect

type tfile = tdecl list

and tdecl = ident * tfunbody

and tfunbody = param list * annot * texpr

and tatom = {a_content : tcatom; a_utyp : ucalctype; a_typ : calctype}

and tcatom =
  | Taunit
  | Tabool of bool
  | Tastring of string
  | Taint of int
  | Taident of ident
  | Taexpr of texpr
  | Tacall of tatom * texpr list
  | Talist of texpr list

and texpr = {content : tcexpr; utyp : ucalctype; typ : calctype}

and tcexpr = 
  | Teblock of tblock
  | Tebexpr of tbexpr

and tbexpr = {b_content : tcbexpr; b_utyp : ucalctype; b_typ : calctype}

and tcbexpr =
  | Tbatom of tatom
  | Tbneg of tbexpr
  | Tbnot of tbexpr
  | Tbbinop of binop * tbexpr * tbexpr
  | Tbassign of ident * tbexpr
  | Tbif of tbexpr * texpr * texpr
  | Tbfn of tfunbody
  | Tbreturn of texpr

and tblock = tstmt list

and tstmt = 
  | Tsbexpr of tbexpr
  | Tsval of ident * texpr
  | Tsvar of ident * texpr

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

let rec calctype_to_string (effect, valtype) =
  let vs = valtype_to_string valtype in
  let ve = effect_to_string effect in
  ve ^ " " ^ vs
  
and valtype_to_string = function
  | Vweak -> "weak"
  | Vunit -> "()"
  | Vbool -> "bool"
  | Vint  -> "int"
  | Vstring -> "string"
  | Vlist v -> "list<" ^ (valtype_to_string v) ^ ">"
  | Vmaybe v -> "maybe<" ^ (valtype_to_string v) ^ ">"
  | Varrow (vl, c) -> 
    let str = ref "(" in
    List.iter (fun v -> str := !str ^ (valtype_to_string v) ^ ", ") vl;
    (if not (List.length vl = 0) then
    str := String.sub !str 0 ((String.length !str) - 2));
    !str ^ ") -> " ^ (calctype_to_string c)

and effect_to_string e =
  match e with
  | Enone -> "<>"
  | Ediv -> "<div>"
  | Econsole -> "<console>"
  | Eall -> "<div, console>"

let rec tatom_to_string ta =
  let typ_str = " type : " ^ calctype_to_string ta.a_typ in
  match ta.a_content with
  | Taunit -> "unit" ^ typ_str
  | Tabool b -> string_of_bool b ^ typ_str
  | Tastring s -> "\"" ^ s ^ "\"" ^ typ_str
  | Taint i -> string_of_int i ^ typ_str
  | Taident id -> id ^ typ_str
  | Taexpr e -> "expr(" ^ texpr_to_string e ^ ")" ^ typ_str
  | Tacall (a, args) ->
    "call(" ^ tatom_to_string a ^ ", [" ^ 
    String.concat ", " (List.map texpr_to_string args) ^ "])" ^ typ_str
  | Talist lst ->
    "list([" ^ String.concat ", " (List.map texpr_to_string lst) ^ "])" ^ typ_str

and texpr_to_string te =
  let typ_str = " type : " ^ calctype_to_string te.typ in
  match te.content with
  | Teblock b -> "block(" ^ tblock_to_string b ^ ")" ^ typ_str
  | Tebexpr b -> "bexpr(" ^ tbexpr_to_string b ^ ")" ^ typ_str

and tblock_to_string stmts = 
  "[" ^ String.concat "; " (List.map tstmt_to_string stmts) ^ "]"

and tstmt_to_string = function
  | Tsbexpr b -> "bexpr(" ^ tbexpr_to_string b ^ ")"
  | Tsval (id, e) -> id ^ " = " ^ texpr_to_string e
  | Tsvar (id, e) -> "var " ^ id ^ " = " ^ texpr_to_string e

and tbexpr_to_string tb =
  let typ_str = " type : " ^ calctype_to_string tb.b_typ in
  match tb.b_content with
  | Tbatom a -> "atom(" ^ tatom_to_string a ^ ")" ^ typ_str
  | Tbneg b -> "neg(" ^ tbexpr_to_string b ^ ")" ^ typ_str
  | Tbnot b -> "not(" ^ tbexpr_to_string b ^ ")" ^ typ_str
  | Tbbinop (op, b1, b2) ->
    "binop(" ^ binop_to_string op ^ ", " ^ 
    tbexpr_to_string b1 ^ ", " ^ tbexpr_to_string b2 ^ ")" ^ typ_str
  | Tbassign (id, b) -> "assign(" ^ id ^ ", " ^ tbexpr_to_string b ^ ")" ^ typ_str
  | Tbif (cond, e1, e2) ->
    "if(" ^ tbexpr_to_string cond ^ ", " ^ texpr_to_string e1 ^ ", " ^ texpr_to_string e2 ^ ")" ^ typ_str
  | Tbfn f -> "fn(" ^ tfunbody_to_string f ^ ")" ^ typ_str
  | Tbreturn e -> "return(" ^ texpr_to_string e ^ ")" ^ typ_str

and tfunbody_to_string (params, annot, e) =
  "[" ^ String.concat ", " (List.map (fun (id, _) -> id) params) ^ "] -> " ^ 
  tannot_to_string annot ^ " : " ^ texpr_to_string e

and tannot_to_string = function
  | Noannot -> "Noannot"
  | Annot (ids, _) -> "Annot(" ^ String.concat ", " ids ^ ")"

let rec tfile_to_string (f : tfile) =
  "File with declarations:\n" ^ 
  String.concat "\n" (List.map tdecl_to_string f)

and tdecl_to_string (id, funbody) =
  "Function " ^ id ^ " -> " ^ tfunbody_to_string funbody
