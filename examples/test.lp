{ p(1;2;3) }.
{ q(1,(2;3)); q(2,1); q(3,1) }.

&odd{ (X+10)-2 : p(X), q(X,Y) }.
&even{ Y : q(X,Y), Y<3 }.
&even{ 1,2 : q(1,2) }.
&odd{ X: p(X) }.
&odd{ X,Y: q(X,Y) }.
&odd{ X : p(X), X!=2 }.
