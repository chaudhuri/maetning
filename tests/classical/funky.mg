% positive a.
% positive b.
% positive c.

%refute (a => a) => (a + ~ a).
%refute ((~ ~ a) => (b + c)) => (((~ ~ a) => b) + ((~ ~ a) => c)).
%refute ~ (a * b) => ~ a + ~ b.
%refute (~ a => ~ b) => b => a.
%refute (a => c) => (~ a => c) => c.
%refute (~ a => b) => (~ a => ~ b) => a.
%refute (a + ~ a => c) => c.
%refute ~ ~ (a + b) => a + b.
%refute (a => (b + c)) => (a => b) + (a => c).
%refute (~ a => (b + c)) => (~ a => b) + (~ a => c).
%refute ~ a + ~ ~ a.
%refute ~ (~ ~ a + ~ a).

%%% The following are also classically false

%refute a + (b * c) => (a + b) * c.
%refute (a => a) => ~ a.
