open Format
open Lexing
open Parser

let usage = "usage: koka [options] file.koka"

let parse_only = ref false
let type_only = ref false

let spec =
  [
    "--parse-only", Arg.Set parse_only, "  stop after parsing";
    "--type-only", Arg.Set type_only,   "  stop after typing"
  ]

let file =
  let file = ref None in
  let set_file s =
    if not (Filename.check_suffix s ".koka") then
      raise (Arg.Bad "no .koka extension");
    file := Some s
  in
  Arg.parse spec set_file usage;
  match !file with Some f -> f | None -> Arg.usage spec usage; exit 1

(* Fonction pour convertir les tokens en chaîne lisible *)
let token_to_string = function
  | Parser.ATM atom -> Printf.sprintf "ATM(%s)" (Ast.catom_to_string atom)  
  | Parser.CMP binop -> Printf.sprintf "CMP(%s)" (Ast.binop_to_string binop)  
  | Parser.LT -> "LT"
  | Parser.GT -> "GT"
  | Parser.IDENT id -> Printf.sprintf "IDENT(%s)" id
  | Parser.IF -> "IF"
  | Parser.ELSE -> "ELSE"
  | Parser.ELIF -> "ELIF"
  | Parser.RETURN -> "RETURN"
  | Parser.FUN -> "FUN"
  | Parser.FN -> "FN"
  | Parser.THEN -> "THEN"
  | Parser.VAL -> "VAL"
  | Parser.VAR -> "VAR"
  | Parser.EOF -> "EOF"
  | Parser.LP -> "LP"
  | Parser.RP -> "RP"
  | Parser.LSQ -> "LSQ"
  | Parser.RSQ -> "RSQ"
  | Parser.LBRACE -> "LBRACE"
  | Parser.RBRACE -> "RBRACE"
  | Parser.COMMA -> "COMMA"
  | Parser.DOT -> "DOT"
  | Parser.COLON -> "COLON"
  | Parser.SCOLON -> "SCOLON"
  | Parser.EQUAL -> "EQUAL"
  | Parser.ASSIGN -> "ASSIGN"
  | Parser.NEGATE -> "NEGATE"
  | Parser.NOT -> "NOT"
  | Parser.ARROW -> "ARROW"
  | Parser.CONCAT -> "CONCAT"
  | Parser.AND -> "AND"
  | Parser.OR -> "OR"
  | Parser.PLUS -> "PLUS"
  | Parser.MINUS -> "MINUS"
  | Parser.TIMES -> "TIMES"
  | Parser.DIV -> "DIV"
  | Parser.MOD -> "MOD"


let rec debug_lexemes lexbuf =
match Lexer.next_token lexbuf with
| Parser.EOF -> print_endline "Token: EOF"
| token ->
    Printf.printf "Lexeme: %s\n" (token_to_string token);
    debug_lexemes lexbuf

let extract_after_last_slash s =
  try
    let last_slash_index = String.rindex s '/' in
    String.sub s (last_slash_index + 1) (String.length s - last_slash_index - 1)
  with Not_found ->
    s 

let () =
let input = open_in file in
let lexbuf = Lexing.from_channel input in
lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file };

try
  let ast = Parser.file Lexer.next_token lexbuf in
  print_endline "Parsing successful!";
  let ast_str = Ast.file_to_string ast in
  Printf.printf "AST:\n%s\n" ast_str;

  (*if !parse_only then (exit 0)
  else (let typed_ast = Typing.type_file ast in
    if !type_only then (exit 0) else (print_endline "Code production isn't implemented yet"; exit 0)
  )*)
   
with  
| Lexer.Lexing_error msg ->
  let curr = lexbuf.lex_curr_p in
  let line = curr.pos_lnum in
  let char_start = curr.pos_cnum - curr.pos_bol in
  let char_end = char_start + String.length (Lexing.lexeme lexbuf) in
  Printf.eprintf "File \"%s\", line %d, characters %d-%d: \n%s\n"
    (extract_after_last_slash file) line char_start char_end msg;
  exit 1
  | Ast.CError msg -> 
    let start_pos = lexbuf.lex_start_p in
    let end_pos = lexbuf.lex_curr_p in
    Printf.eprintf "File \"%s\", line %d, character %d-%d:\n%s \n"
      (extract_after_last_slash file) start_pos.pos_lnum (start_pos.pos_cnum - start_pos.pos_bol)
      (end_pos.pos_cnum - end_pos.pos_bol) msg; exit 1
  | GlobalError msg -> 
    Printf.eprintf "File \"%s\", line 0-0, character 0-0:\n%s \n" msg
  (*| Ast.Typing_error ((start_pos, end_pos), msg) ->
    let line = start_pos.pos_lnum in
    let char_start = start_pos.pos_cnum - start_pos.pos_bol in
    let char_end = end_pos.pos_cnum - end_pos.pos_bol in
    let line_end = end_pos.pos_lnum in
    Printf.eprintf "File \"%s\", line %d-%d, characters %d-%d: \nTyping error: %s\n"
      (extract_after_last_slash file) line line_end char_start char_end msg;
    exit 1*)
  | Parser.Error ->
    let start_pos = lexbuf.lex_start_p in
    let end_pos = lexbuf.lex_curr_p in
    Printf.eprintf "File \"%s\", line %d, character %d-%d:\nsyntax error \n"
      (extract_after_last_slash file) start_pos.pos_lnum (start_pos.pos_cnum - start_pos.pos_bol)
      (end_pos.pos_cnum - end_pos.pos_bol);
    exit 1
  | _ -> exit 2

