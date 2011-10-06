Copyright (C) 2007, Amit Srivastava (asrivas6@uiuc.edu, sriv74@gmail.com)

The following files comprise the Sym Alg distribution:

* [license.txt (Gnu General Public License)][1]
* [symalg.ml (Main source code module)][2]
* [salex.mll (OCamlLex definition file)][3]
* [sayacc.mly (OCamlYacc definition file)][4]

This is a free open source (Gnu General Public License) library which provides
a framework within OCaml to simplify algebraic expressions, rewrite equations
to isolate and/or solve for a variable, and substitute arbitrary expressions
for variables. These functions can be invoked by the user in an interactive
OCaml session or can form the basis for automated equation manipluation and
solving.

In order to use this library, you will need to have the OCaml compiler
installer (ocamlc), the OCamlLex tool (ocamllex), the OCamlYacc tool
(ocamlyacc), and the OCaml toplevel interpreter (ocaml) installed on your
machine.

In case of comments, questions, or suggestions, please contact me at one of
the email addresses listed above. Terms and conditions for the software, build
instructions, the interface specification, and design notes can all be found
in the symalg.ml source file.

Finally, a few examples to illustrate the functionality provided by this
library:

    # print_expr (simplify_expr (parse_expr "(x+1)(x^2-x+1)")));; -> "x^3+1"
    # print_expr (simplify_expr (parse_expr "(4xy-10y^2)/2y^2")));; -> "(2x-
    5y)/(2y)"
    
    # let q1 = parse_eqn "xy - x = 1";;
    # let q2 = parse_eqn "y + 2 = 4/x";;
    # let r1 = show_solve q1 "x";;


Original equation:

    ((x * y) - x) = 1

Equation solved for x:

    x = (1)/(y - 1)

<br/>

    # let r2 = show_substitute q2 "x" (get_rightexpr r1);;


Original equation:

    (y + 2) = (4 / x)

Equation with (1)/(y - 1) substituted for x:

    y + 2 = 4y - 4

<br/>

    # let s2 = show_solve r2 "y";;


Original equation:

    y + 2 = 4y - 4

Equation solved for y:

    y = 2

<br/>

    # let s1 = show_substitute r1 "y" (get_rightexpr s2);;


Original equation:

    x = (1)/(y - 1)

Equation with 2 substituted for y:

    x = 1

   [1]: license.txt
   [2]: symalg.ml
   [3]: salex.mll
   [4]: sayacc.mly
