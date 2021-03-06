%--------------------------------------------------------------------------
% File     : SYN341+1 : ILTP v1.1.2
% Domain   : Syntactic
% Problem  : Church problem 46.15 (6)
% Version  : Especial.
% English  : 

% Refs     : [Chu56] Church (1956), Introduction to Mathematical Logic I
% Source   : [Chu56]
% Names    : 46.15 (6) [Chu56]

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
%            Number of predicates  :    1 (   0 propositional; 3-3 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    4 (   0 singleton;   2 !;   2 ?)
%            Maximal term depth    :    1 (   1 average)

% Comments : 
%--------------------------------------------------------------------------
fof(church_46_15_6,refute,
    ( ? [X1] : 
      ! [X2] : 
      ? [X3] : 
      ! [X4] : 
        ( big_f(X1,X2,X3)
       => big_f(X2,X3,X4) ) )).

%--------------------------------------------------------------------------
