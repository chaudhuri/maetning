% assume end : a7.
%assume O0 : ((b0 + a0) + b0).
%assume O1 : (b0 => ((b1 + a1) + b1)).
%assume O2 : (b1 => ((b2 + a2) + b2)).
%assume O3 : (b2 => ((b3 + a3) + b3)).
%assume O4 : (b3 => ((b4 + a4) + b4)).
%assume O5 : (b4 => ((b5 + a5) + b5)).
%assume O6 : (b5 => ((b6 + a6) + b6)).
%refute a0 + ((b0 & a1) + (((b1 & a2) + (((b2 & a3) + (((b3 & a4) + (((b4 & a5) + (((b5 & a6) + ((b6 & a7))))))))))))).
