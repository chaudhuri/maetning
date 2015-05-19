%--------------------------------------------------------------------------
% File     : SYN723+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : Peter Andrews Problem THM138
% Version  : Especial.
% English  : 

% Refs     : [And97] Andrews (1994), Email to G. Sutcliffe
% Source   : [And97]
% Names    : THM138 [And97]

% Status   : Theorem
% Rating   : 0.67 v3.1.0, 0.83 v2.7.0, 0.67 v2.6.0, 0.50 v2.5.0
%
% Status (intuit.) : Open
% Rating (intuit.) : 1.00 v1.0.0
%
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :   16 (   0 equality)
%            Maximal formula depth :   10 (  10 average)
%            Number of connectives :   15 (   0 ~  ;   0  |;   0  &)
%                                         (  15 <=>;   0 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-1 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   16 (   0 singleton;   8 !;   8 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
fof(thm138,refute,
    ( ? [X] : 
      ! [Y] : 
        ( p(X)
      <=> p(Y) )
  <=> ( ( ? [X] : q(X)
      <=> ! [Y] : r(Y) )
    <=> ( ( ? [X] : 
            ! [Y] : 
              ( q(X)
            <=> q(Y) )
        <=> ( ? [X] : r(X)
          <=> ! [Y] : s(Y) ) )
      <=> ( ? [X] : 
            ! [Y] : 
              ( r(X)
            <=> r(Y) )
        <=> ( ( ? [X] : s(X)
            <=> ! [Y] : p(Y) )
          <=> ( ? [X] : 
                ! [Y] : 
                  ( s(X)
                <=> s(Y) )
            <=> ( ? [X] : p(X)
              <=> ! [Y] : q(Y) ) ) ) ) ) ) )).

%--------------------------------------------------------------------------
