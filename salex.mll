(********************************************************************************
 *
 * Symbolic Algebra Library for OCaml - Lex definition file
 * Copyrigh (C) 2007, Amit Srivastava (asrivas6@uiuc.edu, sriv74@gmail.com)
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 ********************************************************************************)

{
  open Symalg
}

let numeric  = ['0' - '9']
let letter   = ['a' - 'z' 'A' - 'Z']

rule main = parse
  | [' ' '\t' '\n']	{ main lexbuf }  (* skip over whitespace *)

  | "+"			{ PLUS }
  | "-"			{ MINUS }
  | "*"			{ TIMES }
  | "/"			{ DIV }
  | "^"			{ POWER }
  | "("			{ LPAREN }
  | ")"			{ RPAREN }
  | "="			{ EQUALS }

  | ((numeric*) '.' (numeric+)) as n 
               		{ FLOAT (float_of_string n) }

  | (numeric+) as n
				{ FLOAT (float_of_string n) }

  | (letter numeric*) as n
				{ VAR n }

  | eof     		{ EOF } 

{
 let lexer_main = main;;

 let token_iterator_of_string s =
   let rec lbuf = Lexing.from_string s
   in fun () -> lexer_main lbuf;;

 let token_list_of_string s =
   let rec lbuf = Lexing.from_string s 
   and token_list_aux () =
     let token = lexer_main lbuf in
     if token = EOF then
       []
     else
       token :: token_list_aux ()
  in token_list_aux ();;
}
