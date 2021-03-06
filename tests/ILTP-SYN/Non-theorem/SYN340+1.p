%--------------------------------------------------------------------------
% File     : SYN340+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : Church problem 46.15 (5)
% Version  : Especial.
% English  : 

% Refs     : [Chu56] Church (1956), Introduction to Mathematical Logic I
% Source   : [Chu56]
% Names    : 46.15 (5) [Chu56]

% Status   : Theorem
% Rating   : 0.22 v3.1.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.00 v2.1.0
%
% Status (intuit.) : Non-Theorem
% Rating (intuit.) : 0.75 v1.0.0
%
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :    2 (   0 equality)
%            Maximal formula depth :    6 (   6 average)
%            Number of connectives :    1 (   0 ~  ;   0  |;   0  &)
%                                         (   0 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    1 (   0 propositional; 5-5 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    4 (   0 singleton;   1 !;   3 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
fof(church_46_15_5,refute,
    ( ? [X] : 
      ! [Y] : 
      ? [Z1,Z2] : 
        ( big_f(X,Y,Z1,Z2,Z1)
       => big_f(Z1,X,Y,Z1,Z2) ) )).

%--------------------------------------------------------------------------
