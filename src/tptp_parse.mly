(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

%{

  let foo = 42

  let get_forms fn fs = []

  let quantify q vs f =
    let qf v f = match q with
      | `forall -> Form.(forall v (abstract v f))
      | `exists -> Form.(exists v (abstract v f))
    in
    List.fold_right (fun v f -> qf v f) vs f

  let binary bop fl fr =
    match bop with
    | `equiv -> Form.(conj ~pol:NEG [implies [fl] fr ; implies [fr] fl])
    | `nequiv -> Form.(implies [conj ~pol:NEG [implies [fl] fr ; implies [fr] fl]] (disj []))
    | `imp -> Form.(implies [fl] fr)
    | `revimp -> Form.(implies [fr] fl)
    | `nor -> Form.(implies [disj [fl ; fr]] (disj []))
    | `nand -> Form.(implies [conj ~pol:NEG [fl ; fr]] (disj []))

%}

%token LBRACK RBRACK LPAREN RPAREN COMMA COLON DOT
%token VLINE AMPERSAND NOT_EQ TILDE
%token INCLUDE_LPAREN FOF_LPAREN

%token <Idt.t> FORMULA_ROLE
%token <[`forall | `exists]> FOL_QUANTIFIER
%token <[`equiv | `imp | `revimp | `nequiv | `nor | `nand]> BINARY_CONNECTIVE

%token <Idt.t> LIDENT
%token <Idt.t> UIDENT
%token <string> SQUOTE

%start <[`Form of Idt.t * Idt.t * Form.form | `Include of string * Idt.t list]> tptp_input

%%

tptp_input:
| af=annotated_formula DOT { af }
| ins=tptp_include DOT { ins }

%inline annotated_formula:
| f=fof_annotated { f }

fof_annotated:
| FOF_LPAREN n=LIDENT COMMA r=FORMULA_ROLE COMMA f=fof_formula RPAREN
    {  `Form (n, r, f) }

%inline fof_formula:
| f=fof_logic_formula { f }

fof_logic_formula:
| f=fof_binary_formula { f }
| f=fof_unitary_formula { f }

fof_binary_formula:
| f=fof_binary_nonassoc { f }
| f=fof_binary_assoc { f }

fof_binary_nonassoc:
| fl=fof_unitary_formula bop=BINARY_CONNECTIVE fr=fof_unitary_formula
    { binary bop fl fr }

fof_binary_assoc:
| f=fof_or_formula { f }
| f=fof_and_formula { f }

fof_or_formula:
| fl=fof_unitary_formula VLINE fr=fof_unitary_formula { Form.disj [fl ; fr] }
| fl=fof_or_formula VLINE fr=fof_unitary_formula { Form.disj [fl ; fr] }

fof_and_formula:
| fl=fof_unitary_formula AMPERSAND fr=fof_unitary_formula { Form.(conj ~pol:NEG [fl ; fr]) }
| fl=fof_and_formula AMPERSAND fr=fof_unitary_formula { Form.(conj ~pol:NEG [fl ; fr]) }

fof_unitary_formula:
| f=fof_quantified_formula { f }
| f=fof_unary_formula { f }
| f=atomic_formula { f }
| LPAREN f=fof_logic_formula RPAREN { f }

fof_quantified_formula:
| q=FOL_QUANTIFIER LBRACK vs=fof_variable_list RBRACK COLON f=fof_unitary_formula
  { quantify q vs f }

%inline fof_variable_list:
| vs=separated_nonempty_list(COMMA, UIDENT) { vs }

fof_unary_formula:
| uc=unary_connective f=fof_unitary_formula { uc f }
| f=fol_infix_unary { f }

%inline fol_infix_unary:
| tl=term NOT_EQ tr=term { Form.(atom NEG (Idt.intern "!=") [tl ; tr]) }

term:
| t=function_term { t }
| t=UIDENT { Term.(app t []) }

function_term:
| t=plain_term { t }

plain_term:
| t=constant { t }
| f=LIDENT LPAREN ts=arguments RPAREN { Term.(app f ts) }

%inline arguments:
| a=separated_nonempty_list(COMMA,term) { a }

%inline constant:
| f=LIDENT { Term.(app f []) }

tptp_include:
| INCLUDE_LPAREN fn=file_name fs=formula_selection RPAREN
  { `Include (fn, fs) }

%inline file_name:
| fn=SQUOTE { fn }

formula_selection:
| COMMA LBRACK fs=separated_list(COMMA, LIDENT) RBRACK { fs }
| { [] }

%inline atomic_formula:
| t=plain_term {
    match t.Term.term with
    | Term.App (p, ts) -> Form.(atom NEG p ts)
    | _ -> failwith "bad atomic formula"
  }

%inline unary_connective:
| TILDE { fun f -> Form.(implies [f] (disj [])) }
