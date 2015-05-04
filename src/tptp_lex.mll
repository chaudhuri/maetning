(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

{
  module P = Tptp_parse

  exception EOS

  let newline lb =
    Lexing.(
      lb.lex_curr_p <- { lb.lex_curr_p with
        pos_bol = lb.lex_curr_p.pos_cnum ;
        pos_lnum = lb.lex_curr_p.pos_lnum + 1 ;
      }
    )
}

let numeric       = ['0'-'9']
let lower_alpha   = ['a'-'z']
let upper_alpha   = ['A'-'Z']
let alpha_numeric = lower_alpha | upper_alpha | numeric | '_'

let ident         = alpha_numeric*

let space         = ' ' | '\t'
let newline       = '\r''\n' | '\n'

rule token = parse
| '%'              { line_comment lexbuf }
| space            { token lexbuf }
| newline          { newline lexbuf ; token lexbuf }

| "include("       { P.INCLUDE_LPAREN }
| "fof("           { P.FOF_LPAREN }

| '['              { P.LBRACK }
| ']'              { P.RBRACK }
| '('              { P.LPAREN }
| ')'              { P.RPAREN }
| ','              { P.COMMA }
| ':'              { P.COLON }
| '.'              { P.DOT }
| '|'              { P.VLINE }
| '&'              { P.AMPERSAND }
| "!="             { P.NOT_EQ }
| '~'              { P.TILDE }

| '\''             { squote (Buffer.create 19) lexbuf }

| '!'              { P.FOL_QUANTIFIER `forall }
| '?'              { P.FOL_QUANTIFIER `exists }

| "<=>"            { P.BINARY_CONNECTIVE `equiv }
| "=>"             { P.BINARY_CONNECTIVE `imp }
| "<="             { P.BINARY_CONNECTIVE `revimp }
| "<~>"            { P.BINARY_CONNECTIVE `nequiv }
| "~|"             { P.BINARY_CONNECTIVE `nor }
| "~&"             { P.BINARY_CONNECTIVE `nand }

| "axiom"
| "hypothesis"
| "lemma"
| "conjecture"
| "prove"
| "refute"
| "pseudo"         { P.FORMULA_ROLE (Idt.intern (Lexing.lexeme lexbuf)) }

| ident            { let s = Lexing.lexeme lexbuf in
                     if s.[0] == Char.uppercase s.[0]
                     then P.UIDENT (Idt.intern s)
                     else P.LIDENT (Idt.intern s) }

| eof              { raise EOS }

| _                {
  Lexing.(
    Printf.eprintf "Invalid character '%s' at %s, line %d, character %d"
      (String.escaped (lexeme lexbuf))
      (match lexbuf.lex_curr_p.pos_fname with
      | "" -> "<command line>"
      | fin -> fin)
      lexbuf.lex_curr_p.pos_lnum
      (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) ;
    raise P.Error
  )
}

and squote buf = parse
| "\\'"            { Buffer.add_char buf '\'' ; squote buf lexbuf }
| '\''             { P.SQUOTE (Buffer.contents buf) }
| _ as c           { Buffer.add_char buf c ; squote buf lexbuf }

and line_comment = parse
| newline          { newline lexbuf ; token lexbuf }
| eof              { raise EOS }
| _                { line_comment lexbuf }
