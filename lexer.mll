(* Analyseur lexical pour mini-Turtle *)

{
  open Lexing
  open Parser

  (* exception à lever pour signaler une erreur lexicale *)
  exception Lexing_error of string
  type next_tokens_output = Token of token list | Updatestack of int | Updatestackend
  (* note : penser à appeler la fonction Lexing.new_line
     à chaque retour chariot (caractère '\n') *)

  let id_or_kwd = 
  let h = Hashtbl.create 32 in
  List.iter (fun (s, tok) -> Hashtbl.add h s tok)
    ["if", IF; "else", ELSE; "elif", ELIF;
      "return", RETURN; "fun", FUN;
      "fn", FN; "then", THEN;
      "val", VAL; "var", VAR];
  fun s -> try Hashtbl.find h s with Not_found -> IDENT s

  let is_letter = function
    | 'a' .. 'z' -> true
    | 'A' .. 'Z' -> true
    | _ -> false

  let is_digit = function
    | '0' .. '9' -> true
    | _ -> false

  let handle_dash s =
    String.iteri (fun i -> fun c -> 
      if c = '-' then (
        let previous_char = s.[i-1] in
        if is_digit previous_char || is_letter previous_char then (
          if i = (String.length s) - 1 || is_letter s.[i+1] then ()
          else raise (Lexing_error ("dashes in identifiers should be followed by a letter not by " ^ (Char.escaped c)))
        )
        else raise (Lexing_error ("dashes in identifiers should be preceded by a letter or a digit not by " ^ (Char.escaped c)))
      )) s

  let last = ref SCOLON
  let stack = ref [0]
  let string_buffer = Buffer.create 1024

  let end_of_continuation = [PLUS; MINUS; TIMES; DIV; MOD; 
                              LT; (CMP Ble); GT; (CMP Bge);
                              (CMP Beq); (CMP Bneq); 
                              CONCAT; AND; OR; LP; LBRACE; COMMA]

  let start_of_continuation = [PLUS; MINUS; TIMES; DIV; MOD; 
                              LT; (CMP Ble); GT; (CMP Bge);
                              (CMP Beq); (CMP Bneq); 
                              CONCAT; AND; OR; LBRACE; COMMA;
                              THEN; ELSE; ELIF; RP; RBRACE;
                              ARROW; EQUAL; DOT; ASSIGN]
  let rec token_in_list token = function 
    | [] -> false
    | x::s -> x = token || token_in_list token s

  let rec unindent c next = match !stack with
    | m :: _ when m = c ->
      let l_tokens = ref [] in
      if not ((token_in_list !last end_of_continuation) || 
        (token_in_list next start_of_continuation)) 
        then (l_tokens := !l_tokens @ [SCOLON]; last := SCOLON);
      !l_tokens
    | m :: st when m > c -> 
      stack := st;
      if next = RBRACE then SCOLON :: (unindent c next)
      else [SCOLON; RBRACE] @ (unindent c next)
    | _ -> raise (Lexing_error "bad indentation")

  let update_stack c next =
    match !stack with
    | m :: _ when m < c ->
      let l_tokens = ref [] in
      if not ((token_in_list !last end_of_continuation) || 
        (token_in_list next start_of_continuation)) 
        then (l_tokens := !l_tokens @ [LBRACE]; last := LBRACE);
      if !last = LBRACE then stack := c :: !stack;
      !l_tokens
    | _ -> unindent c next

}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let lower = ['a'-'z'] | '_'
let upper = ['A'-'Z']
let other = lower | upper | digit | '-'
let ident = lower other* '''*

let integer = '-'? ('0'| ['1'-'9'] digit*)
let space = ' ' | '\t'
let comment = "//" [^'\n']* | "/*" ([^'*'] | '*' [^'/'])* "*/"

rule next_tokens = parse
  | '\n'? (space | comment)* eof 
            { Updatestackend }
  | '\n'    { new_line lexbuf;Updatestack (indentation lexbuf) }
  | comment { next_tokens lexbuf }
  | space   { next_tokens lexbuf }
  | integer as s 
            { try (Token [ATM (Aint (int_of_string s))])
              with _ -> raise (Lexing_error ("constant too large: " ^ s)) }
  | ident as s
            { handle_dash s; Token [id_or_kwd s] }
  | '='     { Token [EQUAL] }
  | ":="    { Token [ASSIGN] }
  | '~'     { Token [NEGATE] }
  | '!'     { Token [NOT] }
  | "->"    { Token [ARROW] }
  | "++"    { Token [CONCAT] }
  | "&&"    { Token [AND] }
  | "||"    { Token [OR] }
  | '+'     { Token [PLUS] }
  | '-'     { Token [MINUS] }
  | '*'     { Token [TIMES] }
  | "/"     { Token [DIV] }
  | '%'     { Token [MOD] }
  | "=="    { Token [CMP Beq] }
  | "!="    { Token [CMP Bneq] }
  | "<"     { Token [LT] }
  | "<="    { Token [CMP Ble] }
  | ">"     { Token [GT] }
  | ">="    { Token [CMP Bge] }
  | '('     { Token [LP] }
  | ')'     { Token [RP] }
  | '['     { Token [LSQ] }
  | ']'     { Token [RSQ] }
  | '{'     { Token [LBRACE] }
  | '}'     { Token [RBRACE] }
  | ','     { Token [COMMA] }
  | '.'     { Token [DOT] }
  | ':'     { Token [COLON] }
  | ';'     { Token [SCOLON] }
  | '"'     { Token [ATM (Astring (string lexbuf))] }
  | "True"  { Token [ATM (Abool true)]}
  | "False" { Token [ATM (Abool false)]}
  | _ as c  { raise (Lexing_error (Format.sprintf "encountered character %c" c))  }

and indentation = parse
  | (space | comment)* '\n'
      { new_line lexbuf; indentation lexbuf }
  | space* as s
      { String.length s }
  | (space | comment)* comment (space | comment)*
      { raise (Lexing_error "there should not be comments into the indentation") }

and string = parse
  | '"'
      { let s = Buffer.contents string_buffer in
	Buffer.reset string_buffer;
	s }
  | "\\n"
      { Buffer.add_char string_buffer '\n';
	string lexbuf }
  | "\\\""
      { Buffer.add_char string_buffer '"';
	string lexbuf }
  | "\\t"
      { Buffer.add_char string_buffer '\t';
	string lexbuf }
  | "\\\\"
      { Buffer.add_char string_buffer '\\';
	string lexbuf }
  | _ as c
      { Buffer.add_char string_buffer c;
	string lexbuf }
  | eof
      { raise (Lexing_error "unterminated string") }

{

  let next_token =
    let tokens = Queue.create () in (* prochains lexèmes à renvoyer *)
    fun lb ->
      if Queue.is_empty tokens then begin

    let rec refill_queue l_update_stack l_end_token =
      match l_end_token with
      | [] -> 
        let nto = next_tokens lb in
        (match nto with 
        | Updatestackend -> refill_queue (l_update_stack @ [0]) [SCOLON; EOF]
        | Updatestack c -> refill_queue (l_update_stack @ [c]) []
        | Token tl -> refill_queue l_update_stack tl)
      | next::tl -> 
        match l_update_stack with
        | [] -> l_end_token
        | c::s -> (update_stack c next) @ refill_queue s l_end_token
    in 
    let l = refill_queue [] [] in
    let rec last_of_list = function
      | x::[] -> x
      | x::s -> last_of_list s
      | [] -> failwith "Erreur dans le lexer" in
    last := last_of_list l;
    List.iter (fun t -> Queue.add t tokens) l
        end;
        Queue.pop tokens


}