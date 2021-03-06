%--------------------------------------------------------------------------
% File     : SYN731+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : Peter Andrews Problem X2150
% Version  : Especial.
% English  : 

% Refs     : [And97] Andrews (1994), Email to G. Sutcliffe
% Source   : [And97]
% Names    : X2150 [And97]

% Status   : Theorem
% Rating   : 0.22 v3.1.0, 0.00 v2.5.0
%
% Status (intuit.) : Non-Theorem
% Rating (intuit.) : 0.75 v1.0.0
%
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :    2 (   0 equality)
%            Maximal formula depth :    5 (   5 average)
%            Number of connectives :    1 (   0 ~  ;   0  |;   0  &)
%                                         (   0 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    1 (   0 propositional; 3-3 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    4 (   0 singleton;   1 !;   3 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
fof(x2150,refute,
    ( ? [W] : 
        ( ! [X] : 
          ? [Y] : p(W,X,Y)
       => ? [Z] : p(Z,Z,W) ) )).

%--------------------------------------------------------------------------
