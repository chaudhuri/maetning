% From ILTP problem SYN036+2.p
% Intuitionistic status: Open


% fof(pel34,conjecture,
%     ( ( ? [X] :
%         ! [Y] :
%           ( big_p(X)
%         <=> big_p(Y) )
%     <=> ( ? [U] : big_q(U)
%       <=> ! [W] : big_p(W) ) )
%   <=> ( ? [X1] :
%         ! [Y1] :
%           ( big_q(X1)
%         <=> big_q(Y1) )
%     <=> ( ? [U1] : big_p(U1)
%       <=> ! [W1] : big_q(W1) ) ) )).

%negative big_p.
%negative big_q.

%pseudo pp : \A x. big_p(x).
%pseudo pq : \A x. big_q(x).
%refute
     ( ( \E x.
         \A y.
           ( big_p(x)
         <=> big_p(y) )
     <=> ( \E u. big_q(u)
       <=> \A w. big_p(w) ) )
   <=> ( \E x1.
         \A y1.
           ( big_q(x1)
         <=> big_q(y1) )
     <=> ( \E u1. big_p(u1)
       <=> \A w1. big_q(w1) ) ) ).

