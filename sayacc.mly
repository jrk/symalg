%{
(********************************************************************************
 *
 * Symbolic Algebra library for OCaml - Yacc definition file
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

  open Symalg
  #load "symalg.cmo"
%}

%token PLUS MINUS TIMES DIV POWER LPAREN RPAREN EQUALS EOF
%token <float> FLOAT
%token <var>   VAR
%start yacc_eqn
%start yacc_expr
%type <Symalg.eqn>  yacc_eqn
%type <Symalg.expr> yacc_expr

%%
yacc_eqn:
   exp EQUALS exp EOF   { ($1, $3) }

yacc_expr:
   exp EOF              { $1 }

exp:
   op1                  { $1 }

op1:
   op2                  { $1 }
 | op1 PLUS op2         { Node(Plus, [$1; $3]) }
 | op1 MINUS op2        { Node(Minus, [$1; $3]) }

op2:
   op3                  { $1 }
 | op2 TIMES op3        { Node(Times, [$1; $3]) }
 | op2 DIV op3          { Node(Div, [$1; $3]) }

op3:
   op4                  { $1 }
 | op3 op4              { Node(Times, [$1; $2]) }

op4:
   leaf                 { $1 }
 | op4 POWER leaf       { Node(Power, [$1; $3]) }

leaf:
   atom                 { $1 }
 | LPAREN exp RPAREN    { $2 }

atom:
   VAR                  { Leaf(Poly(poly_of_var $1)) }
 | FLOAT                { Leaf(Poly(poly_of_float $1)) }

%%

let eqn_of_string s  = yacc_eqn  lexer_main (Lexing.from_string s);;
let expr_of_string s = yacc_expr lexer_main (Lexing.from_string s);;

let parse_eqn  = eqn_of_string;;
let parse_expr = expr_of_string;;
