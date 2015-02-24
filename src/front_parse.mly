(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

%{
  let lookup_pol h = Form.NEG   (* HACK *)

  let rec make_quant q vs f =
    begin match vs with
    | [] -> f
    | v :: vs -> q v Form.(abstract v (make_quant q vs f))
    end
%}

%token  POSITIVE NEGATIVE ASSUME PSEUDO RETRACT PROVE REFUTE COLON DOT
%token  EOS PREC_MIN
%token  <Idt.t> IDENT
%token  LPAREN COMMA RPAREN
%token  TENSOR PLUS WITH
%token  IF IMP
%token  ONE ZERO TOP
%token  FORALL EXISTS

%nonassoc PREC_MIN
%left     IF
%right    IMP
%left     PLUS
%left     WITH
%left     TENSOR

%start  <Term.term> one_term
%start  <Form.form> one_form
%start  <unit> command
%start  <unit> file

%%

file:
| EOS                        { () }
| command banner file        { () }

banner:
|                            { Format.printf "-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-@." }

command:
| POSITIVE h=IDENT DOT       { Command.register_polarity h Form.POS }
| NEGATIVE h=IDENT DOT       { Command.register_polarity h Form.NEG }
| ASSUME x=IDENT COLON f=form DOT
                             { Command.add_global x f }
| PSEUDO x=IDENT COLON f=form DOT
                             { Command.add_pseudo x f }
| RETRACT x=IDENT DOT        { Command.retract x }
| PROVE f=form DOT           { Command.prove f }
| REFUTE f=form DOT          { Command.refute f }

term:
| head=IDENT args=terms      { Term.(app head args) }
| LPAREN t=term RPAREN       { t }

atom:
| h=IDENT ts=terms           { Form.(atom (Command.lookup_polarity h) h ts) }

form:
| f=atom                     { f }
| f=form TENSOR g=form       { Form.(conj ~pol:POS [f ; g]) }
| ONE                        { Form.(conj ~pol:POS []) }
| f=form PLUS g=form         { Form.(disj [f ; g]) }
| ZERO                       { Form.(disj []) }
| f=form WITH g=form         { Form.(conj ~pol:NEG [f ; g]) }
| TOP                        { Form.(conj ~pol:NEG []) }
| f=form IMP g=form
| g=form IF f=form           { Form.(implies [f] g) }
| FORALL vs=vars DOT f=form
  %prec PREC_MIN             { Form.(make_quant forall vs f) }
| EXISTS vs=vars DOT f=form
  %prec PREC_MIN             { Form.(make_quant exists vs f) }
| LPAREN f=form RPAREN       { f }

one_term:
| t=term EOS                 { t }

one_form:
| f=form EOS                 { f }

%inline terms:
| ts = plist(term)           { ts }

(* combinators *)

%inline plist(X):
| xs = loption (delimited (LPAREN, separated_nonempty_list (COMMA, X), RPAREN)) { xs }

%inline vars:
| vs = separated_nonempty_list (COMMA, IDENT) { vs }
