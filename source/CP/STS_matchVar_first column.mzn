%******SPORT TOURNAMENT SCHEDULING*********

%------------------ variables -----------------------
int: n;
set of int: TEAM = 1..n;
set of int: PERIOD = 1..(n div  2);
set of int: WEEK = 1..(n-1);

% match variable
% 1 if (t1 v t2) in week w
array[TEAM, TEAM, WEEK] of var {0, 1}: M;

% H/A variable
% 1 if team t plays Home in week w
array[TEAM, WEEK] of var {0,1}: H;

% Period variable
% 1 if  team t plays in period p in week w
array[TEAM, PERIOD, WEEK] of var {0, 1}: P;

% ----------- linking variables ---------------------

%if (t1 v t2) is in week w -> they share the same period
%                             and one plays home and the other away
constraint forall(t1, t2 in TEAM where t1 < t2 , w in WEEK)
                 ( ( M[t1,t2,w]==1 )  -> exists(p in PERIOD)( P[t1,p,w]==1 /\ P[t2,p,w]==1));
                 
constraint forall(t1 in TEAM, t2 in TEAM, w in WEEK)
                 ( M[t1,t2,w]==1 -> (( H[t1, w]==1   /\  H[t2, w]==0 ) \/ ( H[t2, w]==1 /\ H[t1, w]==0 ) ) );
  
% ---------------- constraints ----------------------

%even n
constraint (n mod 2) == 0;

% max 2 games in a period
constraint forall(t in TEAM, p in PERIOD) (sum(w in WEEK)(P[t,p,w]) <= 2);

% max 2 teams for every match
constraint forall(p in PERIOD, w in WEEK) (sum(t in TEAM)(P[t,p,w]) = 2);

% exactly 1 game pro week
constraint forall(t in TEAM, w in WEEK) (sum (p in PERIOD)(P[t,p,w]) = 1);

% no match between same team
% we avoid having (t1, t2) couples and we just have ordered pairs (e.g. (1,2), (5,7))
constraint forall(t1 in TEAM, t2 in TEAM, w in WEEK) ((t1>=t2) -> M[t1,t2,w] = 0);

constraint forall(t1, t2 in TEAM where t1<t2) (sum (w in WEEK)(M[t1,t2,w]) = 1);

% -------------- symmetry breaking constraints ----------------

%!!! fix first column (1,2),(3,4)...

% first week games are (1v2),(3v4) ,... H/A not restricted
constraint forall(p in PERIOD)(M[2*p-1,2*p,1]==1);
% first match is (1v2), second is (3v4)..
constraint forall(p in PERIOD) (P[2*p,p,1]==1);
% restriction on H/A
constraint forall(p in PERIOD) (H[2*p,1]==0 /\
                                H[2*p-1,1]==1); %redundant but improving

%first row
%constraint forall(w in WEEK)   (P[w,1,w]==1);

%diagonal team1
%constraint forall(p in PERIOD) ((P[1,p,p]==1) /\ (H[1,p]==1));
% team1 starts home
%constraint forall(i in 1..(n div 2)-1) ( H[1,i] == 1 );

% -------------------- objective function ---------------------

%balance
array[TEAM] of var int: H_matches;
constraint forall(t in TEAM) (H_matches[t] == sum(w in WEEK)(H[t,w]));
var int: balance = sum(t in TEAM) (abs(2*H_matches[t]-(n-1)));

% ---------------------- solve --------------------------------

solve minimize balance;

% -------------------- output ---------------------

output
["\nn: " ++ show(n) ++ "\n"] ++ 
[
  "\nsol: "
] ++
[
  "[" ++
  concat([
    let {
      array[int] of int: home = [t | t in TEAM where fix(P[t,p,w])=1 /\ fix(H[t,w])=1],
      array[int] of int: away = [t | t in TEAM where fix(P[t,p,w])=1 /\ fix(H[t,w])=0]
    } in
    if length(home)=1 /\ length(away)=1 then
      "[" ++ show(home[1]) ++ "," ++ show(away[1]) ++ "]"
    else
      ""
    endif
  | w in WEEK]) ++ "]" ++  % all weeks for fixed p
  if p < max(PERIOD) then "," else "" endif ++ "\n"
| p in PERIOD
] ++
[
  "\nopt: true\n",
  "\nobj: ", show(balance), "\n"
];
