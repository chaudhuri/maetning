(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

{
  module P = Front_parse

  let newline lb =
    Lexing.(
      lb.lex_curr_p <- { lb.lex_curr_p with
        pos_bol = lb.lex_curr_p.pos_cnum ;
        pos_lnum = lb.lex_curr_p.pos_lnum + 1 ;
      }
    )
}

let ident_initial = ['A'-'Z' 'a'-'z']
let ident_body    = ident_initial | ['0'-'9' '_']
let ident         = ident_initial ident_body*

let space         = ' ' | '\t'
let newline       = '\r''\n' | '\n'

rule token = parse
| "%positive"      { P.POSITIVE }
| "%negative"      { P.NEGATIVE }
| "%assume"        { P.ASSUME }
| "%pseudo"        { P.PSEUDO }
| "%retract"       { P.RETRACT }
| "%prove"         { P.PROVE }
| "%refute"        { P.REFUTE }

| '%'              { line_comment lexbuf }

| space            { token lexbuf }
| newline          { newline lexbuf ; token lexbuf }

| ident            { P.IDENT (Idt.intern (Lexing.lexeme lexbuf)) }

| '*' | "\\tensor" { P.TENSOR }
| '1' | "\\one"    { P.ONE }
| '+' | "\\plus"   { P.PLUS }
| '0' | "\\zero"   { P.ZERO }

| "#F" | "#f"      { P.ZERO }
| "\\bot"          { P.ZERO }
| "&" | "\\with"   { P.WITH }
| "#T" | "#t"
| "\\top"          { P.TOP }

| "=>"             { P.IMP }
| "<="             { P.IF }

| "\\A"            { P.FORALL }
| "\\E"            { P.EXISTS }

| ','              { P.COMMA }
| '.'              { P.DOT }
| '('              { P.LPAREN }
| ')'              { P.RPAREN }
| ':'              { P.COLON }

| eof              { P.EOS }
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

and line_comment = parse
| newline          { newline lexbuf ; token lexbuf }
| eof              { P.EOS }
| _                { line_comment lexbuf }
