(********************************************************************************
 *
 * OCaml Symbolic Algebra library, Version 1.0
 * Copyright (C) 2007, Amit Srivastava (asrivas6@uiuc.edu, sriv74@gmail.com)
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
 ********************************************************************************
 *
 * This module provides a framework within OCaml to simplify algebraic
 * expressions, rewrite equations to isolate and/or solve for a variable, and
 * substitute arbitrary expressions for variables.  These functions can be
 * invoked by the user in an interactive OCaml session or can form the basis for
 * automated equation manipluation and solving.
 *
 * Since this module does not compile to a standalone executable, a Makefile is
 * not provided.  Also, since construction the expressions and equations by hand
 * is quite tedious, a lexer (salex.mll) and parser (sayacc.mly) are provided to
 * minimize this burden.
 *
 * To build the components, execute the following instructions from the command
 * shell:
 * > ocamlc -c symalg.ml
 * > ocamllex salex.mll
 * > ocamlyacc sayacc.mly
 *
 * To invoke the library from the OCaml top-level, enter the following:
 * > ocaml (following commands are initiated from within OCaml)
 * # #use "salex.ml";;
 * # #use "sayacc.ml";;
 *
 * Note if you follow this sequence and use the lexer/parser, then there is no
 * no need to #use this file (symalg.ml) because it is loaded by sayacc.ml.
 *
 ********************************************************************************
 *
 * The primary top-level interface functions are:
 *   parse_expr      - string -> expr                 - e.g. let e  = parse_expr "(x+1)(x^2-x+1)";;
 *   parse_eqn       - string -> eqn                  - e.g. let q  = parse_eqn  "(4xy-10y^2)/2y^2=0-z";;
 *   simplify_expr   - expr -> expr                   - e.g. let es = simplify_expr e;;
 *   simplify_eqn    - eqn -> eqn                     - e.g. let qs = simplify_eqn q;;
 *   solve           - eqn -> string -> eqn           - e.g. let i  = solve q "x";;
 *   get_leftexpr/
 *   get_rightexpr   - eqn -> expr                    - e.g. let (l,r) = (get_leftexpr i, get_rightexpr i);;
 *   substitute_expr - expr -> string -> expr -> expr - e.g. let en = substitute_expr e "x" (parse_expr "y^2");;
 *   substitute_eqn  - expr -> string -> expr -> expr - e.g. let qn = substitute_eqn q "y" (parse_expr "2");;
 *   print_expr      - expr -> string                 - e.g. let ep = print_expr es;;
 *   print_eqn       - eqn -> string                  - e.g. let qp = print_eqn i;;
 *
 * There are also a few simple wrappers that call these functions and display old/new values:
 *    show_simplify   - calls simplify_expr
 *    show_solve      - calls solve
 *    show_substitute - calls substitute_eqn
 *
 * A few catches/limitations to be aware of:
 *
 * In order to keep the lexer/parser straightforward, the "-" character is always
 * treated as a minus operator rather than negation.  To represent a negative
 * value, simply prepend zero (i.e. use "0-x" or "0-3" in place of "-x" or "-3".
 *
 * The greatest common divisor algorithm only finds monomial divisors, not
 * polynomials.  In other words, the library can simplify (4xy-10y^2)/2y^2 to
 * (2x-5y)/2y, but cannot simplify (x^2-1)/(x-1) to x+1.  The Grobner basis
 * method is one way to extend the GCD algorithm to find polynomial divisors.
 *
 * The library does not support imaginary and complex numbers, nor functions
 * such as log, exp, sin, cos, etc.  Adding functional support should be
 * straightforward, the key change being to add the inverse operations to the
 * isolate_eqn_one_level function.
 *
 * When applying the square root operation to both sides, only the positive
 * square root is retained.  In other words, given the equation (x-3)^2=4, the
 * solver will replace this with x-3=2 and compute x=5.  A better solution would
 * be to allow the solve routine to generate a list of equations, in this case
 * x-3=2 and x-3=-2, which would then produce both roots x=5 and x=1.
 *
 * Since the focus is on symbolic methods, numerical root-finding techniques such
 * as Newton's method, the bisection method, and the quadratic equation are not
 * implemented.
 *
 ********************************************************************************
 *
 * Below is an example session illustrating the steps by which one could solve
 * a system of simultaneous equations.  Note these are non-linear equations and
 * do not lend themselves to standard techniques such as Gaussian elimination or
 * Cramer's method (determinants).  This example scrapes the surface of the power
 * of symbolic manipulation.  These statements can be put into a function to
 * automate the process (for example, the demo function show_solve_simul at the
 * bottom of this file does precisely that).
 *
 * # let q1 = parse_eqn "xy - x = 1";;
 * # let q2 = parse_eqn "y + 2 = 4/x";;
 * # let r1 = show_solve q1 "x";;
 *
 * Original equation:
 * ((x * y) - x) = 1
 * Equation solved for x:
 * x = (1)/(y - 1)
 *
 * # let r2 = show_substitute q2 "x" (get_rightexpr r1);;
 *
 * Original equation:
 * (y + 2) = (4 / x)
 * Equation with (1)/(y - 1) substituted for x:
 * y + 2 = 4y - 4
 *
 * # let s2 = show_solve r2 "y";;
 *
 * Original equation:
 * y + 2 = 4y - 4
 * Equation solved for y:
 * y = 2
 *
 * # let s1 = show_substitute r1 "y" (get_rightexpr s2);;
 *
 * Original equation:
 * x = (1)/(y - 1)
 * Equation with 2 substituted for y:
 * x = 1
 *
 ********************************************************************************
 *
 * If you simply invoke the top-level interface, then the internal representation
 * probably won't matter.  If you want to extend the library, here is a breakdown
 * of the hierarchy of defined types:
 *
 * Variable - one of two leaf tokens in the parse tree (the other being float).
 *   The lexer identifies variable names as consisting of one letter followed
 *   by zero or more numbers.  Therefore "ab" will never parse as one variable
 *   and will instead parse as the product of variables "a" and "b".
 *
 * Power - a variable raised to a constant (float) power.  Negative and
 *   fractional values are allowed.  Any variable can be represented with
 *   by setting the power to 1.  Note that constants cannot be represented,
 *   nor the product of two powers (e.g. x^2y^3).
 *
 * Monomial - the product of a constant coefficient and a list of power terms,
 *   e.g. 3xy^2.  Note any constant can be represented with a coefficient and
 *   an empty list of power terms, and any power can be represented with a
 *   coefficient of 1 and a single-element list.  The power terms in a simplified
 *   monomial are sorted in alphabetical order based on variable name.  Monomials
 *   are closed under the operations of multiplication, division, and raising to
 *   a constant power.
 *
 * Polynomial - the sum of a list of monomials, e.g. 3x^2y + y^3 - 4.  Note any
 *   monomial can be represented with a single-element list.  The monomials in
 *   a simplified polynomial are sorted on variable name and exponent (earlier
 *   alphabetical order and/or higher exponent cause term to appear on left).
 *   Polynomials are closed under the operations of addition, subtraction, and
 *   multiplication. Polynomials also constitute the basic unit of operation in
 *   this library (all tokens are parsed to polynomials, and the simplest type
 *   that appears in an expression tree is a polynomial).
 *
 * Fraction - the ratio of two polynomials, e.g. (x+1)/(y+z).  Note any polynomial
 *   can be represented with a denominator of 1.  Fractions are closed under the
 *   operations of addition, subtraction, multiplication, and division, and
 *   represent the second type that can appear in an expression tree (only
 *   after simplification).
 *
 * Exponential - one fraction raised to the power of another fraction, e.g.
 *   (x+y)^(z/(1-z)).  Note any fraction can be represented with an exponent of 1.
 *   Exponentials are closed under raising to any power corresponding to the
 *   fraction type, and represent the final basic type that can appear in an
 *   expression tree (only after simplification).
 *
 * Term - leaf of the expression tree, can be a polynomial, fraction, or
 *   exponential.
 *
 * Node - interior element of the expression tree, represented by an operation
 *  (Plus, Minus, Times, Div, or Power) and a list of operands which themselves
 *   are either terms or nodes.
 *
 * Expression - Top-level expression, represented by a term (leaf), or node
 *   (tree) containing child expressions.  Note that if the power (exponentiation)
 *   operation is not present, then simplification will always yield a single leaf
 *   containing a polynomial or fraction.  Since exponentials are not closed
 *   under most operations, exponentiation can lead to simplified expressions of
 *   arbitrary complexity (but always with the same or fewer elements than the
 *   original expression tree).  Node operands are sorted by expression type
 *   (nodes before terms) and then term types (exponentials, then fractions,
 *   and lastly polynomials).
 *
 * Equation - Statement asserting equality of two expressions.  Equations are
 *   transformed by applying the same operations to both expressions.
 *)

(****************************************
 * Type definitions
 ****************************************)
type operator = Plus | Minus | Times | Div | Power;;

type var = string;;                     (* e.g. "x", "y", etc. *)
type power = var * float;;              (* var, raised_to, e.g. ("x", 3.) -> x^3. *)
type monomial = float * power list;;    (* coefficient, list of power terms, e.g. (2., [("x", 1.); ("y", 3.)]) -> 2xy^3 *)
type polynomial = monomial list;;       (* sum of monomials, e.g. [(2., [("x", 2.); ("y", 3.)]); (-1., [])] -> 2x^2y^3 - 1 *)
type frac = polynomial * polynomial;;   (* numerator, denominator *)
type exp = frac * frac;;                (* base, exponent *)
type term = Poly of polynomial
          | Frac of frac
          | Exp of exp;;
type expr = Leaf of term
          | Node of operator * expr list;;
type eqn = expr * expr;;

(****************************************
 * Lexer/Parser definitions
 ****************************************)
type token = PLUS | MINUS | TIMES | DIV | POWER | LPAREN | RPAREN | EQUALS
           | FLOAT of float
           | VAR of var
           | EOF;;

(****************************************
 * Data accessors
 ****************************************)
let get_first p = match p with (f, s) -> f;;
let get_second p = match p with (f, s) -> s;;

(* power accessors *)
let get_var p       = get_first p;;
let get_raisedto p  = get_second p;;

(* monomial accessors *)
let get_coeff m     = get_first m;;
let get_powerlist m = get_second m;;

(* fraction accessors *)
let get_numer f     = get_first f;;
let get_denom f     = get_second f;;

(* exponential accessors *)
let get_base e      = get_first e;;
let get_exponent e  = get_second e;;

(* node accessors *)
let get_operator n  = get_first n;;
let get_operands n  = get_second n;;

(* equation accessors *)
let get_leftexpr e  = get_first e;;
let get_rightexpr e = get_second e;;

(****************************************
 * General-purpose utility functions
 ****************************************)
let get_first_of_list lst =
  match lst with
    []    -> failwith "Empty list"
  | x::xs -> x;;

let get_rest_of_list lst =
  match lst with
    []    -> failwith "Empty list"
  | x::xs -> xs;;

let get_last_of_list lst =
  let rec get_last_of_list_helper so_far lst =
    match lst with
      []    -> so_far
    | x::xs -> get_last_of_list_helper x xs
  in match lst with
    []    -> failwith "Empty list"
  | x::xs -> get_last_of_list_helper x xs;;

(* Determine if fraction portion of float is 0 *)
let is_float_int f = float_of_int (int_of_float f) = f;;

(* Determine if integer is even or odd *)
let is_even i =
  let q = i / 2 in
  let r = i - q * 2 in
  r = 0;;

(* Compute a^b via a^b = exp(b * log a).  Note that log a is only
   defined if a > 0, so there are special cases for a = 0 and a < 0 *)

let power a b =
  if a > 0. then
    exp (b *. log a)
  else if a = 0. then
    0.
  else if is_float_int b then
    let i = int_of_float b in
    let p = exp (b *. log (-.a)) in   (* compute (-a)^b *)
    if is_even i then p else -.p      (* now fix sign *)
  else
    failwith ("Cannot raise negative number " ^ string_of_float a ^ " to non-integer power " ^ string_of_float b);;

(* Euclidean GCD (greatest common denominator) algorithm - works on ints *)
let rec gcd a b =
  let q = a / b in
  let r = a - b * q in
  if r = 0 then abs b else gcd b r;;

let list_contains lst i = List.fold_left (||) false (List.map (fun x -> x = i) lst);;
let intersect_list a b  = List.fold_right (@) (List.map (fun x -> if list_contains a x then [x] else []) b) [];;
let intersect_diff a b  = List.fold_right (@) (List.map (fun x -> if list_contains a x then [] else [x]) b) [];;

(****************************************
 * String conversion routines
 ****************************************)
let string_of_float_enh f = if is_float_int f then string_of_int (int_of_float f) else string_of_float f

let string_of_power p =
  let v = get_var p in
  let r = get_raisedto p in
  if r = 1. then v else v ^ "^" ^ string_of_float_enh r;;

let rec string_of_powerlist pl =
  match pl with
    []    -> ""
  | x::xs -> string_of_power x ^ string_of_powerlist xs;;

let string_of_mono m =
  let c = get_coeff m in
  let pl = get_powerlist m in
  let absc = abs_float c in
  let pls = string_of_powerlist pl in
  (if c >= 0. then "" else "-") ^
  (if absc = 1. && List.length pl > 0 then "" else string_of_float_enh absc) ^
  pls;;

let string_of_poly p =
  let rec string_of_poly_helper lst =
    match lst with
      []          -> ""
    | (c, pl)::xs ->
        let absc = abs_float c in
        let pls = string_of_powerlist pl in
        (if c >= 0. then " + " else " - ") ^
        (if absc = 1. && List.length pl > 0 then "" else string_of_float_enh absc) ^
        pls ^ string_of_poly_helper xs

  in match p with
    []    -> ""
  | x::xs -> string_of_mono x ^ string_of_poly_helper xs;;

let string_of_frac_multi_line f =
  let n = get_numer f in
  let d = get_denom f in
  let ns = string_of_poly n in
  let ds = string_of_poly d in

  if ds = "1" then   (* Frac with denom of 1 gets converted to poly, but not if part of exponential *)
    ns
  else
    let rec string_of_dashes n = if n = 0 then "" else "-" ^ string_of_dashes (n - 1) in
    let m = max (String.length ns) (String.length ds) in
    ns ^ "\n" ^ string_of_dashes m ^ "\n" ^ ds;;

let string_of_frac f =
  let n = get_numer f in
  let d = get_denom f in
  let ns = string_of_poly n in
  let ds = string_of_poly d in
  if ds = "1" then ns else "(" ^ ns ^ ")/(" ^ ds ^ ")";;   (* Frac with denom of 1 gets converted to poly, but not if part of exponential *)

let string_of_exp e =
  let b = get_base e in
  let e = get_exponent e in
  "(" ^ string_of_frac b ^ ")^(" ^ string_of_frac e ^ ")";;

let string_of_term t =
  match t with
    Poly p      -> string_of_poly p
  | Frac (n, d) -> string_of_frac (n, d)
  | Exp (b, e)  -> string_of_exp (b, e);;

let string_of_operator o =
  match o with
    Plus  -> " + "
  | Minus -> " - "
  | Times -> " * "
  | Div   -> " / "
  | Power -> " ^ ";;

let rec string_of_expr e =
  match e with
    Leaf f -> string_of_term f
  | Node (o, el) ->
      let rec loop lst =
        match lst with
          []    -> ""
        | x::xs -> string_of_operator o ^ string_of_expr x ^ loop xs in

      match el with
        [] -> ""
      | x::xs -> "(" ^ string_of_expr x ^ loop xs ^ ")";;

let string_of_eqn q = (string_of_expr (get_leftexpr q)) ^ " = " ^ (string_of_expr (get_rightexpr q));;

let string_of_exprlist el =
  let rec string_of_exprlist_helper el =
    match el with
      []    -> ""
    | x::xs -> string_of_expr x ^ ";" ^ string_of_exprlist_helper xs in

  "[" ^ string_of_exprlist_helper el ^ "]";;

let print_expr e = string_of_expr e;;
let print_eqn  q = string_of_eqn q;;

(****************************************
 * Expression identification/extraction
 ****************************************)
let get_expr_type e =
  match e with
    Leaf _ -> 1
  | Node _ -> 2;;

let get_term_type t =
  match t with
    Poly _ -> 1
  | Frac _ -> 2
  | Exp _  -> 3;;

let is_term e =
  match e with
    Leaf _ -> true
  | _      -> false;;

let term_of_expr e =
  match e with
    Leaf t -> t
  | _      -> failwith ("Cannot convert expr " ^ string_of_expr e ^ " to term");;

let is_node e =
  match e with
    Node _ -> true
  | _      -> false;;

let node_of_expr e =
  match e with
    Node (o, el) -> (o, el)
  | _            -> failwith ("Cannot convert expr " ^ string_of_expr e ^ " to node");;

let get_terms el = List.fold_right (@) (List.map (fun x -> if is_term x then [term_of_expr x] else []) el) [];;
let get_nodes el = List.fold_right (@) (List.map (fun x -> if is_node x then [node_of_expr x] else []) el) [];;

let include_terms_type tl t = List.fold_right (@) (List.map (fun x -> if get_term_type x = t then [x] else []) tl) [];;
let exclude_terms_type tl t = List.fold_right (@) (List.map (fun x -> if get_term_type x != t then [x] else []) tl) [];;

let include_nodes_type nl o = List.fold_right (@) (List.map (fun x -> if get_operator x = o then [x] else []) nl) [];;
let exclude_nodes_type nl o = List.fold_right (@) (List.map (fun x -> if get_operator x != o then [x] else []) nl) [];;

let expr_of_term t = Leaf t;;
let expr_of_node n = Node(get_operator n, get_operands n);;

(****************************************
 * Lexigraphical ordering routines
 ****************************************)
let compare_power a b =
  let avar = get_var a in
  let bvar = get_var b in

  (* Compare variable *)
  if avar < bvar then
    true
  else if avar > bvar then
    false
  else

    (* Compare raised to term *)
    get_raisedto a >= get_raisedto b;;

let compare_powerlist al bl =
  let avars = List.fold_left (^) "" (List.map get_var al) in
  let bvars = List.fold_left (^) "" (List.map get_var bl) in

  (* Special check for coefficient term - empty variable list *)
  if avars = "" then
    false
  else if bvars = "" then
    true
  else

  (* Compare variables *)
    if avars < bvars then
      true
    else if avars > bvars then
      false
    else

    (* Compare raised to terms, one by one *)
      let rec compare_raisedto_loop al bl =
        match al with
          []    -> true
        | x::xs ->
            (match bl with
              []    -> false
            | y::ys ->
                let araisedto = get_raisedto x in
                let braisedto = get_raisedto y in
                if araisedto > braisedto then
                  true
                else if araisedto < braisedto then
                  false
                else
                  compare_raisedto_loop xs ys)

      in compare_raisedto_loop al bl;;

let compare_mono a b = compare_powerlist (get_powerlist a) (get_powerlist b);;
let compare_term a b = get_term_type a >= get_term_type b;;

let compare_expr a b =
  let at = get_expr_type a in
  let bt = get_expr_type b in
  if at > bt then
    true
  else if at < bt then
    false
  else if is_term a then
    compare_term (term_of_expr a) (term_of_expr b)
  else
    true;;

let find_leftmost compare lst =
  let rec leftmost_helper compare so_far lst =
    match lst with
      []    -> so_far
    | x::xs -> leftmost_helper compare (if compare so_far x then so_far else x) xs

  in let rec leftmost_remove leftmost so_far lst =
    match lst with
      []    -> None
    | x::xs -> if x = leftmost then Some(x, so_far@xs) else leftmost_remove leftmost (so_far@[x]) xs

  in match lst with
    []    -> None
  | x::xs -> leftmost_remove (leftmost_helper compare x xs) [] lst;;

let rec sort compare lst =
  match find_leftmost compare lst with
    None         -> []
  | Some (x, xs) -> x::(sort compare xs);;

(****************************************
 * Monomial algebra
 ****************************************)
let mono_of_float f = (f, []);;
let mono_of_var v   = (1., [(v, 1.)]);;

let is_mono_float m = List.length (get_powerlist m) = 0;;
let float_of_mono m = if is_mono_float m then get_coeff m else failwith ("Cannot convert monomial " ^ string_of_mono m ^ " to float");;

(* If coefficient of mono is zero, then remove variable list *)
let simplify_mono m =
  let c = get_coeff m in
  let pl = get_powerlist m in

  if c = 0. then
    mono_of_float 0.   (* 0xy -> 0 *)
  else
    (c, List.fold_right (@) (List.map (fun x -> if get_raisedto x = 0. then [] else [x]) pl) []);; (* x^0, y^0, etc. can be dropped *)

(* Find power term in power list corresponding to requested variable - fails if variable not found*)
let rec get_power pl v =
  match pl with
    []    -> failwith ("Cannot find variable " ^ v ^ " in powerlist " ^ string_of_powerlist pl)
  | x::xs -> if get_var x = v then x else get_power xs v;;

(* Multiply list of power terms by another power term *)
let mult_powerlist_power pl p =
  let rec mult_powerlist_power_helper pl p so_far =
    match pl with
      []    -> so_far @ [p]
    | x::xs ->
        if get_var x = get_var p then
          so_far @ [(get_var x, get_raisedto x +. get_raisedto p)] @ xs    (* x^m * x^n -> x^(m+n) *)
        else
          mult_powerlist_power_helper xs p (so_far @ [x])                  (* x^m * y^n can't be merged, so append to power list *)

  in mult_powerlist_power_helper pl p [];;

(* Multiply list of power terms by another list of power terms *)
let mult_powerlist_powerlist pl1 pl2 =
  let rec mult_powerlist_powerlist_helper pl1 pl2 =
    match pl2 with
      []    -> pl1
    | x::xs -> mult_powerlist_powerlist_helper (mult_powerlist_power pl1 x) xs

  in sort compare_power (mult_powerlist_powerlist_helper pl1 pl2);;

(* Multiply monomial by monomial *)
let mult_mono m1 m2 = simplify_mono (get_coeff m1 *. get_coeff m2, mult_powerlist_powerlist (get_powerlist m1) (get_powerlist m2));;   (* ax * by = (ab)xy *)

(* Raise power term by a constant power *)
let raise_power_power p n = (get_var p, get_raisedto p *. n);;     (* (x^m)^n -> x^(mn) *)

(* Raise monomial by a constant power *)
let raise_power_mono m n = (power (get_coeff m) n,
  List.map (fun x -> raise_power_power x n) (get_powerlist m));;   (* [a(x^b)(y^c)]^n -> (a^n)(x^(bn))(y^(cn)) *)

(* Compute negative (additive inverse) to transform subtraction into addition *)
let negate_mono m = mult_mono m (-1., []);;                        (* -(axy) -> (-a)xy *)

(* Compute reciprocal (multiplicative inverse) to transform division into multiplication *)
let invert_mono m = raise_power_mono m (-1.);;                     (* 1/[a(x^m)(y^n)] -> (a^-1)(x^-m)(y^-n) *)

(* Compute greatest common divisor of two lists of power terms - e.g. gcd(x^3y^2z, x^2z^2) = x^2z *)
let gcd_powerlist pl1 pl2 =
  let rec gcd_powerlist_helper pl1 pl2 intvars so_far =
    match intvars with
      []    -> so_far
    | x::xs ->
      let p1 = get_raisedto (get_power pl1 x) in
      let p2 = get_raisedto (get_power pl2 x) in

      if is_float_int p1 && is_float_int p2 then
        gcd_powerlist_helper pl1 pl2 xs (so_far @ [(x, min p1 p2)])
      else
        gcd_powerlist_helper pl1 pl2 xs so_far

  in gcd_powerlist_helper pl1 pl2 (intersect_list (List.map get_var pl1) (List.map get_var pl2)) [];;

(* Compute greatest common divisor of two monomials - e.g. gcd(12x^3y^2z, 8x^2z^2) = 4x^2z *)
let gcd_mono m1 m2 =
  let f1 = get_coeff m1 in
  let f2 = get_coeff m2 in
  let gcd_coeff =
    if is_float_int f1 && is_float_int f2 then
      float_of_int (gcd (int_of_float f1) (int_of_float f2))
    else
      1. in
  (gcd_coeff, gcd_powerlist (get_powerlist m1) (get_powerlist m2));;

(****************************************
 * Polynomial algebra
 ****************************************)
let is_term_poly t =
  match t with
    Poly _ -> true
  | _      -> false;;

let poly_of_term t =
  match t with
    Poly p -> p
  | _      -> failwith ("Cannot convert term " ^ string_of_term t ^ " to polynomial");;

let is_poly_float p = List.length p = 1 && is_mono_float (get_first_of_list p);;
let is_term_float t = is_term_poly t && is_poly_float (poly_of_term t);;

let poly_of_mono m  = [m];;
let poly_of_float f = poly_of_mono (mono_of_float f);;
let poly_of_var v   = poly_of_mono (mono_of_var v);;

let float_of_poly p = if is_poly_float p then float_of_mono (get_first_of_list p) else failwith ("Cannot convert polynomial " ^ string_of_poly p ^ " to float");;
let float_of_term t = if is_term_float t then float_of_poly (poly_of_term t) else failwith ("Cannot convert term " ^ string_of_term t ^ "to float");;

(* If constant term is zero and there is at least one non-zero monomial, remove zero constant *)
let simplify_poly p =
  if List.length p = 0 then        (* All terms eliminated, put in constant zero *)
    poly_of_float 0.
  else if List.length p = 1 then   (* Single term, even if zero we don't want to eliminate *)
    p
  else
    let last = get_last_of_list p in
    if get_coeff last = 0. && List.length (get_powerlist last) = 0 then   (* Zero constant term with non-zero terms, eliminate constant *)
      List.fold_right (@) (List.map (fun x -> if List.length (get_powerlist x) = 0 then [] else [x]) p) []
    else
      p;;

(* Add monomial to polynomial *)
let add_poly_mono p m =
  let rec add_poly_mono_helper p m so_far =
    match p with
      []    -> m::so_far
    | x::xs ->
        if get_powerlist x = get_powerlist m then
          let c = get_coeff x +. get_coeff m in                               (* axy + bxy -> (a + b)xy *)
          if c = 0. then so_far @ xs else (c, get_powerlist x)::so_far @ xs   (* if coefficient is zero, drop monomial from list *)
        else
          add_poly_mono_helper xs m (x::so_far)   (* ax + by can't be merged, so append to monomial list *)
  in add_poly_mono_helper p m [];;

(* Add polynomial to polynomial *)
let add_poly p1 p2 =
  let rec add_poly_helper p1 p2 =
    match p2 with
      []    -> p1
    | x::xs -> add_poly_helper (add_poly_mono p1 x) xs
  in simplify_poly (sort compare_mono (add_poly_helper p1 p2));;

(* Multiply polynomial by monomial *)
let rec mult_poly_mono p m =
  match p with
    []    -> []
  | x::xs -> (mult_mono x m)::(mult_poly_mono xs m);;   (* (a+b)c = ac + bc *)

(* Multiply polynomial by polynomial *)
let mult_poly p1 p2 =
  let rec mult_poly_helper p1 p2 =
    match p2 with
      []    -> []
    | x::xs -> (mult_poly_mono p1 x) @ (mult_poly_helper p1 xs)   (* (a+b)(c+d) -> (a+b)c + (a+b)d -> ac + ad + bc + bd *)
  in let mono_list = mult_poly_helper p1 p2
  in List.fold_left add_poly (poly_of_float 0.) (List.map poly_of_mono mono_list);;

(* Compute negative (additive inverse) to transform subtraction into addition *)
let rec negate_poly p =
  match p with
    []    -> []
  | x::xs -> (negate_mono x)::(negate_poly xs);;   (* -(ax+by) -> (-ax)+(-by) *)

(* GCD of polynomial is simplify GCD iterated on all monomials *)
let gcd_poly p1 p2 =
  let ml = p1 @ p2 in
  List.fold_left gcd_mono (get_first_of_list ml) (get_rest_of_list ml);;

(****************************************
 * Fraction algebra
 ****************************************)
let frac_of_poly p = (p, poly_of_float 1.);;   (* p -> fraction (p / 1) *)

(* Polynomials and fractions can be converted into fractions *)
let frac_of_term t =
  match t with
    Poly p      -> frac_of_poly p
  | Frac (n, d) -> (n, d)
  | _           -> failwith ("Cannot convert term " ^ string_of_term t ^ " to fraction");;

(* Add fraction to fraction *)
let add_frac f1 f2 =
  let n1 = get_numer f1 in
  let d1 = get_denom f1 in
  let n2 = get_numer f2 in
  let d2 = get_denom f2 in
  (add_poly (mult_poly n1 d2) (mult_poly n2 d1), mult_poly d1 d2);;   (* a/b + c/d -> (ad+bc)/bd *)

(* Multiply fraction by fraction *)
let mult_frac f1 f2 =
  let n1 = get_numer f1 in
  let d1 = get_denom f1 in
  let n2 = get_numer f2 in
  let d2 = get_denom f2 in
  (mult_poly n1 n2, mult_poly d1 d2);;   (* a/b * c/d -> ac/bd *)

(* Compute negative (additive inverse) to transform subtraction into addition *)
let negate_frac f =
  let n = get_numer f in
  let d = get_denom f in
  (negate_poly n, d);;   (* -(a/b) -> (-a)/b *)

(* Compute reciprocal (multiplicative inverse) to transform division into multiplication *)
let invert_frac f =
  let n = get_numer f in
  let d = get_denom f in
  (d, n);;   (* 1/(a,b) -> b/a *)

(****************************************
 * Exponential algebra
 ****************************************)
let exp_of_frac f = (f, frac_of_poly (poly_of_float 1.));;   (* f -> exponential (f ^ 1) *)

(* Polynomials, fractions, and exponentials can be converted into exponentials *)
let exp_of_term t =
  match t with
    Poly p      -> exp_of_frac (frac_of_poly p)
  | Frac (n, d) -> exp_of_frac (n, d)
  | Exp (b, e)  -> (b, e);;

(* Raise exponential by power represented by fraction *)
let raise_power_exp e f =
  let b = get_base e in
  let e = get_exponent e in
  (b, mult_frac e f);;   (* (a^b)^c = a^(bc) *)

(* Compute reciprocal (multiplicative inverse) to transform division into multiplication *)
let invert_exp e = raise_power_exp e (frac_of_poly (poly_of_float (-1.)));;

(****************************************
 * Expression/Equation simplification
 ****************************************)

(* Compute negative (additive inverse) to transform subtraction into addition *)
let negate_term t =
  match t with
    Poly p      -> Leaf(Poly(negate_poly p))
  | Frac (n, d) -> Leaf(Frac(negate_frac (n, d)))
  | Exp (b, e)  -> Node(Times, [Leaf(Exp(b, e)); Leaf(Poly(poly_of_float(-1.)))]);;

let negate_expr e =
  match e with
    Leaf t       -> negate_term t
  | Node (o, el) -> Node(Times, [Node(o, el); Leaf(Poly(poly_of_float(-1.)))]);;

(* Compute reciprocal (multiplicative inverse) to transform division into multiplication *)
let invert_term t =
  match t with
    Poly p      -> Leaf(Frac(poly_of_float 1., p))
  | Frac (n, d) -> Leaf(Frac(invert_frac (n, d)))
  | Exp (b, e)  -> Leaf(Exp(invert_exp (b, e)));;

let invert_expr e =
  match e with
    Leaf t       -> invert_term t
  | Node (o, el) -> Node(Div, [Leaf(Poly(poly_of_float(1.))); Node(o, el)]);;

(* Recursively simplify expression by replacing complex subexpressions with simpler
   subexpressions or leaves *)
let rec simplify_expr e =
  match e with
    Leaf t ->
      (match t with
        Frac (n, d) ->
          let p = mult_poly n (poly_of_mono (invert_mono (get_first_of_list d))) in
          let powerlists = List.fold_right (@) (List.map get_powerlist p) [] in

          (* If single monomial in denominator, and after dividing all exponents
             are non-negative, then rewrite (ax + by) / d as ax/d + by/d *)

          if List.length d = 1 && (List.fold_left (&&) true (List.map (fun p -> get_raisedto p >= 0.) powerlists)) then
            Leaf(Poly(p))

          else   (* Can't eliminate denominator, but we'll cancel out common terms *)
            let gcd = gcd_poly n d in
            let newn = mult_poly n (poly_of_mono (invert_mono gcd)) in
            let newd = mult_poly d (poly_of_mono (invert_mono gcd)) in
            Leaf(Frac(newn, newd))

      | _           -> e)

  | Node (o, el) ->
      let sel         = List.map simplify_expr el in
      let nodes       = get_nodes sel in
      let terms       = get_terms sel in

      let same_nodes  = include_nodes_type nodes o in
      let diff_nodes  = exclude_nodes_type nodes o in
      let child_exprs = List.fold_right (@) (List.map get_operands same_nodes) [] in

      (* For Plus and Times, we can eliminate child nodes of the same type and pull those expressions up to this level *)
      let new_nodes   = if o = Plus || o = Times then diff_nodes @ (get_nodes child_exprs) else nodes in
      let new_terms   = if o = Plus || o = Times then terms @ (get_terms child_exprs) else terms in

      let poly_terms  = include_terms_type new_terms 1 in
      let frac_terms  = include_terms_type new_terms 2 in
      let exp_terms   = include_terms_type new_terms 3 in

      (match o with
        Plus ->
          if List.length sel < 2 then
            failwith ("Plus operation requires at least 2 operands, operand list = " ^ string_of_exprlist sel)
          else
            let new_poly_frac_expr =
              if List.length frac_terms > 0 then       (* If any fractions are present, add all polys and fracs to get new frac *)
                [simplify_expr (Leaf(Frac(List.fold_left add_frac (frac_of_poly (poly_of_float 0.)) (List.map frac_of_term (poly_terms @ frac_terms)))))]

              else if List.length poly_terms > 0 then  (* No fractions present, add all polys to get new poly *)
                [Leaf(Poly(List.fold_left add_poly (poly_of_float 0.) (List.map poly_of_term poly_terms)))]

              else                                     (* Exponentials only, nothing to simplify *)
                [] in

            (* If new term evaluated to zero, we prepare in case we should eliminate this extraneous term *)
            let simp_expr = if List.length new_poly_frac_expr = 1 && is_term_float (term_of_expr (get_first_of_list new_poly_frac_expr)) &&
                              float_of_term (term_of_expr (get_first_of_list new_poly_frac_expr)) = 0. then [] else new_poly_frac_expr in

            let repl_terms = sort compare_term (exp_terms @ (List.map term_of_expr simp_expr)) in
            let repl_exprs = sort compare_expr ((List.map expr_of_node new_nodes) @ (List.map expr_of_term repl_terms)) in

            if List.length repl_exprs > 1 then
              Node(Plus, repl_exprs)
            else if List.length repl_exprs = 1 then
              get_first_of_list repl_exprs
            else
              Leaf(Poly(poly_of_float 0.))   (* No terms, so we restore the 0. float value that we eliminated *)

      | Minus ->
          if List.length sel != 2 then
            failwith ("Minus operation requires exactly 2 operands, operand list = " ^ string_of_exprlist sel)
          else
            let first  = get_first_of_list sel in
            let second = get_first_of_list (get_rest_of_list sel) in
            simplify_expr (Node(Plus, [first; negate_expr second]))   (* a - b = a + (-b) *)

      | Times ->
          if List.length sel < 2 then
            failwith ("Times operation requires at least 2 operands, operand list = " ^ string_of_exprlist sel)
          else
            let new_poly_frac_expr =
              if List.length frac_terms > 0 then       (* If any fractions are present, multiply all polys and fracs to get new frac *)
                [simplify_expr (Leaf(Frac(List.fold_left mult_frac (frac_of_poly (poly_of_float 1.)) (List.map frac_of_term (poly_terms @ frac_terms)))))]

              else if List.length poly_terms > 0 then  (* No fractions present, multiply all polys to get new poly *)
                [Leaf(Poly(List.fold_left mult_poly (poly_of_float 1.) (List.map poly_of_term poly_terms)))]

              else                                     (* Exponentials only, nothing to simplify *)
                [] in

            (* If new term evaluated to zero, we replace this entire node with zero *)
            if List.length new_poly_frac_expr = 1 && is_term_float (term_of_expr (get_first_of_list new_poly_frac_expr)) &&
              float_of_term (term_of_expr (get_first_of_list new_poly_frac_expr)) = 0. then
              Leaf(Poly(poly_of_float 0.))   (* 0x = 0 *)

            else
              (* If new term evaluated to one, we prepare in case we should eliminate this extraneous term *)
              let simp_expr = if List.length new_poly_frac_expr = 1 && is_term_float (term_of_expr (get_first_of_list new_poly_frac_expr)) &&
                                float_of_term (term_of_expr (get_first_of_list new_poly_frac_expr)) = 1. then [] else new_poly_frac_expr in

              let repl_terms = sort compare_term (exp_terms @ (List.map term_of_expr simp_expr)) in
              let repl_exprs = sort compare_expr ((List.map expr_of_node new_nodes) @ (List.map expr_of_term repl_terms)) in

              if List.length repl_exprs > 1 then
                Node(Times, repl_exprs)
              else if List.length repl_exprs = 1 then
                get_first_of_list repl_exprs
              else
                Leaf(Poly(poly_of_float 1.))   (* No terms, so we restore the 1. float value that we eliminated *)

      | Div ->
          if List.length sel != 2 then
            failwith ("Divide operation requires exactly 2 operands, operand list = " ^ string_of_exprlist sel)
          else
            let first  = get_first_of_list sel in
            let second = get_first_of_list (get_rest_of_list sel) in

            if List.length poly_terms = 2 then
              simplify_expr (Leaf(Frac(poly_of_term (term_of_expr first), poly_of_term (term_of_expr second))))
            else
              simplify_expr (Node(Times, [first; invert_expr second]))   (* a / b = a * (1 / b) *)

      | Power ->
          if List.length sel != 2 then
            failwith ("Power operation requires exactly 2 operands, operand list = " ^ string_of_exprlist sel)
          else
            let first  = get_first_of_list sel in
            let second = get_first_of_list (get_rest_of_list sel) in
            let second_float = is_term second && is_term_float (term_of_expr second) in

            if second_float && float_of_term (term_of_expr second) = 0. then
              Leaf(Poly(poly_of_float 1.))   (* a ^ 0 -> 1 *)

            else if second_float && float_of_term (term_of_expr second) = 1. then
              first                          (* a ^ 1 -> a *)

            else if List.length poly_terms = 2 then
              let first_poly  = poly_of_term (term_of_expr first) in
              let second_poly = poly_of_term (term_of_expr second) in

              if List.length first_poly = 1 && second_float then   (* Monomial raised to constant power is monomial *)
                Leaf(Poly(poly_of_mono (raise_power_mono (get_first_of_list first_poly) (float_of_poly second_poly))))
              else
                Leaf(Exp(frac_of_poly first_poly, frac_of_poly second_poly))

            else if List.length poly_terms + List.length frac_terms = 2 then
              let first_frac  = frac_of_term (term_of_expr first) in
              let second_frac = frac_of_term (term_of_expr second) in
              Leaf(Exp(first_frac, second_frac))

            else if is_term first && get_term_type (term_of_expr first) = 3 then   (* Exp term, employ (a^b)^c -> a^(bc) *)
              let exp = exp_of_term (term_of_expr first) in
              let base = get_base exp in 
              let exponent = get_exponent exp in
              simplify_expr (Node(Power, [Leaf(Frac(base)); Node(Times, [Leaf(Frac(exponent)); second])]))

            else if is_node first && get_operator (node_of_expr first) == Power then   (* Power node, employ (a^b)^c -> a^(bc) *)
              let operands = get_operands (node_of_expr first) in
              let base = get_first_of_list operands in
              let exponent = get_first_of_list (get_rest_of_list operands) in
              simplify_expr (Node(Power, [base; Node(Times, [exponent; second])]))

            else
              e
      );;

(* Simplify equation by simplifying expressions on both sides *)
let simplify_eqn q = (simplify_expr (get_leftexpr q), simplify_expr (get_rightexpr q));;

(****************************************
 * Expression expansion (unsimplification)
 *   The requirement is to that leaves
 *   should only consist of floats and
 *   variables, and all other terms will
 *   be replaced by nodes, with dummy
 *   operands added as needed.
 ****************************************)
let expand_mono m =
  let c         = get_coeff m in       (* Convert coefficient to separate polynomial term *)
  let pl        = get_powerlist m in   (* Convert each power in powerlist to separate polynomial term *)
  let c_poly    = Leaf(Poly(poly_of_float c)) in
  let pl_polys  = List.map (fun p -> Leaf(Poly(poly_of_mono (1., [p])))) pl in
  let new_exprs = c_poly::pl_polys in

  if List.length new_exprs = 1 then
    Node(Times, Leaf(Poly(poly_of_float 1.))::new_exprs)   (* Multiply by 1 to get node with two terms *)
  else
    Node(Times, new_exprs);;

let expand_poly p =
  let new_exprs = List.map expand_mono p in

  if List.length new_exprs = 1 then
    Node(Plus, Leaf(Poly(poly_of_float 0.))::new_exprs)   (* Add 0 to get node with two terms *)
  else
    Node(Plus, new_exprs);;

let expand_frac f = Node(Div, [expand_poly (get_numer f); expand_poly (get_denom f)]);;
let expand_exp e  = Node(Power, [expand_frac (get_base e); expand_frac (get_exponent e)]);;

let expand_term t =
  match t with
    Poly p      -> expand_poly p
  | Frac (n, d) -> expand_frac (n, d)
  | Exp (b, e)  -> expand_exp (b, e)

let rec expand e =
  match e with
    Leaf t       -> expand_term t
  | Node (o, el) -> Node(o, List.map expand el);;

(****************************************
 * Equation rewriting/solving
 ****************************************)
let contains_poly p v =
  let m = get_first_of_list p in
  let pl = get_powerlist m in
  let vars = List.map get_var pl in
  let intvars = intersect_list vars [v] in
  List.length intvars = 1;;

let rec contains_expr e v =
  match e with
    Leaf t       -> contains_poly (poly_of_term t) v
  | Node (o, el) -> List.fold_left (||) false (List.map (fun e -> contains_expr e v) el);;

(* Standard algebra rules, apply same operation to both sides of equation *)
let add_expr_eqn e q    = (Node(Plus, [get_leftexpr q; e]), Node(Plus, [get_rightexpr q; e]));;
let sub_expr_eqn e q    = (Node(Minus, [get_leftexpr q; e]), Node(Minus, [get_rightexpr q; e]));;
let mult_expr_eqn e q   = (Node(Times, [get_leftexpr q; e]), Node(Times, [get_rightexpr q; e]));;
let div_expr_eqn e q    = (Node(Div, [get_leftexpr q; e]), Node(Div, [get_rightexpr q; e]));;
let raise_power_eqn e q = (Node(Power, [get_leftexpr q; e]), Node(Power, [get_rightexpr q; e]));;

let invert_eqn q =
  let left  = get_leftexpr q in
  let right = get_rightexpr q in
  (Node(Div, [Leaf(Poly(poly_of_float 1.)); left]), Node(Div, [Leaf(Poly(poly_of_float 1.)); right]));;

(* Repeatedly apply same operations to both sides of equation, for all expressions in list *)
let rec op_exprlist_eqn op el q =
  match el with
    [] -> q
  | x::xs -> op_exprlist_eqn op xs (op x q);;

(* Perform a single pass at the current node level, moving all terms containing the variable to the
   left and all terms not containing the variable to the right *)
let rec isolate_eqn_one_level q v =
  let r = get_rightexpr q in
  let left = expand (get_leftexpr q) in
  let right = expand r in

  if contains_expr right v then
    isolate_eqn_one_level (simplify_eqn (sub_expr_eqn r q)) v
  else
    match left with
      Leaf _       -> failwith "Expression expansion failed"
    | Node (o, el) ->
        let noncontain_exprs = List.fold_right (@) (List.map (fun e -> if not (contains_expr e v) then [e] else []) el) [] in
        let rewritten =
          (match o with
            Plus  -> op_exprlist_eqn sub_expr_eqn noncontain_exprs q

          | Minus ->
              let first  = get_first_of_list el in
              let second = get_first_of_list (get_rest_of_list el) in
              let newq1  = if not (contains_expr first v) then sub_expr_eqn first q else q in
              let newq2  = if not (contains_expr second v) then add_expr_eqn second newq1 else newq1 in
              newq2

          | Times -> op_exprlist_eqn div_expr_eqn noncontain_exprs q

          | Div   ->
              let first  = get_first_of_list el in
              let second = get_first_of_list (get_rest_of_list el) in

              (* If right side is zero, we will always multiple both sides by divisor term to get rid of it *)
              let rzero  = is_term r && is_term_float (term_of_expr r) && float_of_term (term_of_expr r) = 0. in
              let newq1  = if not (contains_expr first v) then div_expr_eqn first q else q in
              let newq2  = if (rzero || not (contains_expr second v)) then mult_expr_eqn second newq1 else newq1 in
              newq2

          | Power ->
              let second = get_first_of_list (get_rest_of_list el) in
              if contains_expr second v then
                q
              else
                raise_power_eqn (invert_expr second) q) in

        simplify_eqn rewritten;;

(* The isolate_eqn_one_level function can strip away a top level node and reveal further opportunities to isolate
   the variable among the child nodes, so this function keeps calling isolate_eqn_one_level until no more terms
   can be moved *)
let isolate_eqn q v =
  let rec isolate_eqn_helper q v =
    let rewritten = isolate_eqn_one_level q v in
    if rewritten = q then q else isolate_eqn_helper rewritten v

  in isolate_eqn_helper q v;;

(* Isolate all terms containing variable, then attempt to reduce left side to single term containing only the variable *)
let rec solve q v =
  let isolated = isolate_eqn q v in
  let left     = get_leftexpr isolated in
  let right    = get_rightexpr isolated in

  if is_term left then
    let term = term_of_expr left in

    match term with
      Poly p ->
        let divisor = mult_poly p (poly_of_mono (invert_mono (mono_of_var v))) in   (* See if we can divide to leave var by itself *)
          if (contains_expr (expand (Leaf(Poly(divisor)))) v) then
            isolated
          else
            (Leaf(Poly(poly_of_mono (mono_of_var v))), simplify_expr (Node(Div, [right; Leaf(Poly(divisor))])))

    | Frac (n, d) ->
        let numer_contains = contains_expr (expand (Leaf(Poly(n)))) v in
        let denom_contains = contains_expr (expand (Leaf(Poly(d)))) v in
        if numer_contains && denom_contains then
          isolated
        else if numer_contains then
          solve (Leaf(Poly(n)), Node(Times, [right; Leaf(Poly(d))])) v   (* n/d = r -> n = rd *)
        else
          solve (Leaf(Poly(d)), Node(Div, [Leaf(Poly(n)); right])) v     (* n/d = r -> d = n / r *)

    | Exp (b, e) ->
        if contains_expr (expand (Leaf(Frac(e)))) v then
          isolated
        else
          solve (Leaf(Frac(b)), Node(Power, [right; Leaf(Frac(invert_frac e))])) v   (* b^e = r -> b = r^(1/e) *)

  else
    isolated;;

(* Determine if variable is by itself on left-side of equation *)
let is_isolated e v =
  let l = get_leftexpr e in
  if is_term l then
    let t = term_of_expr l in
    if is_term_poly t then
      let p = poly_of_term t in
      if List.length p = 1 then
        let m = get_first_of_list p in
        let c = get_coeff m in
        let pl = get_powerlist m in
        if c = 1. && List.length pl = 1 then
          let p        = get_first_of_list pl in
          let var      = get_var p in
          let raisedto = get_raisedto p in
          var = v && raisedto = 1.
        else
          false
       else
         false
    else
      false
  else
    false;;

(****************************************
 * Expression/Equation substitution
 ****************************************)
let substitute_poly p v n =
  let m = get_first_of_list p in
  let pl = get_powerlist m in
  let vars = List.map get_var pl in
  let intvars = intersect_list vars [v] in
  if List.length intvars = 1 then
    let p = get_power pl v in
    Node(Power, [n; Leaf(Poly(poly_of_float (get_raisedto p)))])
  else
    Leaf(Poly(p));;

let rec substitute_expr e v n =
  match e with
    Leaf t       -> substitute_poly (poly_of_term t) v n
  | Node (o, el) -> Node(o, List.map (fun e -> substitute_expr e v n) el);;

let substitute e v n     = simplify_expr (substitute_expr (expand e) v n);;
let substitute_eqn q v n = (substitute (get_leftexpr q) v n, substitute (get_rightexpr q) v n);;

(****************************************
 * Routines to display result with before and after
 ****************************************)
let show_simplify e =
  let s = simplify_expr e in
  print_string "\nOriginal expression:\n";
  print_string ((string_of_expr e) ^ "\n");
  print_string "Simplified expression:\n";
  print_string ((string_of_expr s) ^ "\n\n");
  s;;

let show_solve q v =
  let r = solve q v in
  print_string "\nOriginal equation:\n";
  print_string ((string_of_eqn q) ^ "\n");
  print_string ("Equation solved for " ^ v ^ ":\n");
  print_string ((string_of_eqn r) ^ "\n\n");
  r;;

let show_substitute q v n =
  let s = substitute_eqn q v n in
  print_string "\nOriginal equation:\n";
  print_string ((string_of_eqn q) ^ "\n");
  print_string ("Equation with " ^ string_of_expr n ^ " substituted for " ^ v ^ ":\n");
  print_string ((string_of_eqn s) ^ "\n\n");
  s;;

let show_solve_simul q1 q2 v1 v2 =
  let r1 = show_solve q1 v1 in

  if is_isolated r1 v1 then
    let r2 = show_substitute q2 v1 (get_rightexpr r1) in
    let s2 = show_solve r2 v2 in

    if is_isolated s2 v2 then
      let s1 = show_substitute r1 v2 (get_rightexpr s2) in
      (s1, s2)
    else
      failwith ("Failed to solve equation " ^ string_of_eqn s2 ^ " for variable " ^ v2)
  else
    failwith ("Failed to solve equation " ^ string_of_eqn q1 ^ " for variable " ^ v1);;
