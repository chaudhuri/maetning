% --------------------------------------------------------------------------
% File     : SYN081+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : Pelletier Problem 59
% Version  : Especial.
% English  : 

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
%          : [Hah94] Haehnle (1994), Email to G. Sutcliffe
% Source   : [Hah94]
% Names    : Pelletier 59 [Pel86]

% Status   : Theorem
% Rating   : 0.00 v2.1.0
%
% Status (intuit.) : Open
% Rating (intuit.) : 1.00 v1.0.0
%
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :    4 (   0 equality)
%            Maximal formula depth :    4 (   4 average)
%            Number of connectives :    4 (   2 ~  ;   0  |;   1  &)
%                                         (   1 <=>;   0 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    1 (   0 propositional; 1-1 arity)
%            Number of functors    :    1 (   0 constant; 1-1 arity)
%            Number of variables   :    2 (   0 singleton;   1 !;   1 ?)
%            Maximal term depth    :    2 (   2 average)

% Comments : 
% --------------------------------------------------------------------------
% fof(pel59_1,axiom,
%    ( ! [X] : 
%        ( big_f(X)
%      <=> ~ big_f(f(X)) ) )).

% fof(pel59,conjecture,
%    ( ? [X] : 
%        ( big_f(X)
%        & ~ big_f(f(X)) ) )).

   
%negative g.

%assume ax : \A x.  ( g(x) <=> ~ g(f(x)) ) .
%pseudo p : (\E x. g(f(x))) => (\A x. g(f(x))).


% The following seems to loop indefinitely in Mætning version 0.2.0-dev:
%refute \E x . ( g(x) & ~ g(f(x)) ) .

  
%--------------------------------------------------------------------------
