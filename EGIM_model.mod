
#SETS
set SM dimen 2;
set P; # Producer
set P2;# Producer has LNG terminal
set C; #Consumer Country
set C2;#Consumer has LNG regassification
set LCs{C} ;#set of s in c
set LCm{C} ;#set of m in c
set LCe{C} ;#set of e in c
set LC{c in C}=LCs[c] union LCm[c] union LCe[c] ; # Consumer Country Spot Market and Mid-stream
set M; # Midstreamer
set S; #Spot Market
set E; #End-user
set Z;# Sectors (Household/Industry/Power)
set R;#Transportation Method (Pipeline/LNG)
set L;# Potential LNG terminal
set K;# Potential Pipeline
set W= K union L;# All Potential Project
set PC{R} dimen 2;#set of pairs(p,c) via transportation method r
set PCk dimen 3;#set of pairs(p,c) via potential pipeline k
set CC dimen 2;# set of pair(c,c) via pipeline
set CCk dimen 3 ;# set of pair(c,c) via potential pipeline
set A{R} dimen 2; #set of all
set Alt{R} dimen 2;# set of arc connects from p to n long-term via r
set Ap{k in R}={(i,j) in A[k] union Alt[k] ,r in R: k==r};
set Yset dimen 4; #{origin,destiny,from,to}
set Ylt dimen 3;# set of arc connects from p to n long-term via r
set Yset_IC dimen 2;# set of arc interconnection 
set T; # Years
set Dt{T}; # Days of year t
set NM;
set artis;


set LA1 dimen 3; #Longterm pipeline not direct connected
set LA2 dimen 3; #Longterm pipeline direct connected
set LA = LA1 union LA2;


set TCon = setof {(i,j,k,l) in Yset:l<>j} (l);
set Ymid{Ylt};

#PARAMETERS

param D;
param Dis{1..D};#Discount factor month to month
param c_PR {P} >= 0; #Unit production cost
param c_PM1 {Alt[1] union A[1] union setof {(i,j,k) in Ylt} (i,j)}==36;#Unit trasportation cost
param c_PM21 {A[2] union Alt[2]}>=0;#Unit trasportation cost
param c_PM22 {A[2] union Alt[2] }>=0;#Unit trasportation cost
param c_PM23 {A[2] union Alt[2] }>=0;#Unit trasportation cost
param c_INVp {M}>=0; #Unit cost of injection
param c_INVm {M} >= 0; #Unit cost of withdrawn
param c_INV {M} >= 0; #Unit cost of holding gas one day in storage
param f{W}>=0; # Fixed investment cost
param C_R {P} >=0 ;#Reserve capacity [bcm]
param C_PR{P} >=0; #Daily production capacity[bcm/day]
param C_LQ{P2} >=0; #Daily liqufication capacity [bcm/day]
param C_RQ{C2} >=0; #Daily regassificaiton capacity[bcm/day] of Consumer Country
param C_PRQ{C2,L} >=0; #Daily potential regassificaiton capacity[bcm/day]
param C_PL{CC union PC[1]} >=0; # Daily pipeline capacity of all arc [bcm/day]
param C_PPL{CCk union PCk} >=0; # Daily potential pipeline capacity of all arc [bcm/day]
param C_INV{M} >=0; #Total inventory capacity[bcm]
param C_INVp{M} >=0; #Daily injection capacity[bcm/day]
param C_INVm{M} >=0; #Daily withdrawn capacity[bcm/day]
#param C_T{P,E}>=0; # Marginal cost from producer to end-user
param II0{M} >=0; #Initial inventory volume [bcm]
param alp{P2} >=0; # Rate of liquefaction loss[%]
param beta{C2} >=0; # Rate of regasification loss[%]
param B{T} >=0; # Annual Budget [$/year]
param R_G{P} >=0; # Geopolitical risk 
param R_D{PC[1] union PC[2]} >=0; #Distance risk 
param R_F{R} >=0; #Fungibility index
param R_ ; #Maximum risk index
param LT{LA,T};# Longterm contract volume
param a{E,Z,1..D};
param b{E,Z,1..D};
param weig;
param nm1:=1;
param nm2:=1;
#param LI{E,S}; # Lerner index limit for end-user sectors 


#VARIABLE

var  z{W,T} binary;#LNG or Pipeline activation 
var  ax{M,1..D} binary;#Storage
var  x{Ap[1] union Ap[2] ,1..D}>=0 ; #Amount of natural gas transfered from node i to j
var	 y{Yset,1..D}>=0;#Amount of natural gas transfered from node i to j for transfer origin to destiny
var  I{M,1..D}>=0 ; #Amount of gas in storage
var  Ip{M,1..D}>=0 ; #Amount of gas injected
var  Im{M,1..D}>=0 ; #Amount of gas withdrawn
var  d{E,Z,1..D}>=0 ; #Amount of gas demand
#var  yy{E,Z,1..D,1..6} binary ; #Amount of gas demand
var zx{E,Z,1..D}>=0;


#MODEL

#MR=MC
maximize social_welfare:sum{t in 1..D}(Dis[t]*(sum{e in E,s in Z}(0.5*b[e,s,t]*(d[e,s,t]**2)+a[e,s,t]*d[e,s,t])
											 -sum{r in R,p in P,(p,j) in A[r] union Alt[r]}(c_PR[p]*x[p,j,r,t])
											 -sum{(o,des,j,k) in Yset, r in R:(o,des,r) in Ylt && o==j}((c_PR[o]+c_PM1[o,des])*y[o,des,j,k,t])
											 -sum{(i,j) in A[1] union Alt[1]}c_PM1[i,j]*x[i,j,1,t]
											 -weig*sum{(i,j) in A[2] union Alt[2] }(c_PM21[i,j]*x[i,j,2,t]+c_PM22[i,j]*x[i,j,2,t]**2+c_PM23[i,j])
											 -sum{j in M}(c_INVp[j]*Ip[j,t]+c_INVm[j]*Im[j,t]+c_INV[j]*I[j,t])));
											 
subject to res{i in P}:sum{r in R, (i,j) in A[r] union Alt[r],t in 1..D}x[i,j,r,t]+ sum{(i,des,i,k) in Yset,t2 in 1..D}y[i,des,i,k,t2] <= C_R[i];

subject to pro_cap{i in P,t in 1..D}:sum{r in R, (i,j)in A[r] }x[i,j,r,t]+sum{(i,des,i,k) in Yset}y[i,des,i,k,t] <= C_PR[i]/12;

subject to lng_cap1{i in P2,t in 1..D}: sum{(i,j) in A[2] union Alt[2]}x[i,j,2,t] <= C_LQ[i];

subject to lng_cap2{c in C2 ,t in T,dt in 1..D}: sum{j in LCm[c] union LCs[c],(i,j) in A[2] union Alt[2]}((1-alp[i])*x[i,j,2,dt]) <= C_RQ[c]+sum{k in L,o in 1 .. t}C_PRQ[c,k]*z[k,o];

subject to pipe_cap{(c1,c2) in CC ,t in T,dt in Dt[t]}:sum{j1 in LCm[c1],j2 in LCs[c2]}x[j1,j2,1,dt]+sum{j3 in LCs[c1],j4 in LCm[c2]}x[j3,j4,1,dt]
													  +sum{(p,m,c1,c2) in Yset}y[p,m,c1,c2,dt]+sum{(p2,m2,c1,j4) in Yset:m2 == j4 }y[p2,m2,c1,j4,dt]
													   <= C_PL[c1,c2]+sum{(c1,c2,k) in CCk,o in 1 .. t}C_PPL[c1,c2,k]*z[k,o];

subject to pipe_cap2{(p,c) in PC[1] ,t in T,dt in Dt[t]}:sum{(p,j) in A[1] union Alt[1] :j in LCs[c] union LCm[c] }x[p,j,1,dt]+sum{(p,m,p,c) in Yset}y[p,m,p,c,dt]<= C_PL[p,c]+sum{(p,c,k) in PCk,o in 1 .. t}C_PPL[p,c,k]*z[k,o];

subject to one_inv{k in W}: sum{t in T}z[k,t]<=1;

subject to sto1{c in C, m in LCm[c],t in 1..D}: Ip[m,t]
										  -sum{(i,m) in A[1] union Alt[1]}x[i,m,1,t]
										  -sum{(p,m,k,m)in Yset}y[p,m,k,m,t]
										  -sum{(i,m) in A[2] union Alt[2]}((1-alp[i])*(1-beta[c])*x[i,m,2,t])
										  +sum{(m,j) in A[1]}x[m,j,1,t] >=0 ;

subject to sto2{c in C, m in LCm[c],t in 1..D}: Im[m,t]
										  +sum{(i,m) in A[1] union Alt[1]}x[i,m,1,t]
										  +sum{(i,m) in A[2] union Alt[2]}((1-alp[i])*(1-beta[c])*x[i,m,2,t])
										  +sum{(p,m,k,m)in Yset}y[p,m,k,m,t]
										  -sum{(m,j) in A[1]}x[m,j,1,t] >=0 ;
										  

subject to sto3{j in M,t in 2..D}: I[j,t]-I[j,t-1]-Ip[j,t]+Im[j,t] =0 ;

subject to sto4{j in M,t in 1..D}: I[j,t]<= C_INV[j];

subject to sto5{j in M,t in 1..D}: Ip[j,t]<= C_INVp[j]*(ax[j,t]);

subject to sto6{j in M,t in 1..D}: Im[j,t]<= C_INVm[j]*(1-ax[j,t]);

subject to sto7{j in M}: I[j,1]= II0[j];


subject to eql1{c in C,s in LCs[c],t in 1..D}:sum{(i,s) in A[1]}x[i,s,1,t]+sum{(i,s) in A[2]}((1-alp[i])*(1-beta[c])*x[i,s,2,t])-sum{r in R,(s,j) in A[r]}x[s,j,r,t]=0;

subject to eql2{e in E,t in 1..D}:sum{(m,e) in A[1]}x[m,e,1,t]-sum{s in Z}d[e,s,t]=0;

subject to eql21{e in E,t in 1..D}:sum{(m,e) in A[1]}x[m,e,1,t]*0.18<=d[e,1,t];

subject to eql22{e in E,t in 1..D}:sum{(m,e) in A[1]}x[m,e,1,t]*0.13<=d[e,2,t];

subject to eql23{e in E,t in 1..D}:sum{(m,e) in A[1]}x[m,e,1,t]*0.15<=d[e,3,t];

subject to budget{t in T}: sum{k in W }f[k]*z[k,t]<= B[t]+sum{k in W,t2 in 1..t-1 }(B[t2]-f[k]*z[k,t2]);

subject to budget0{t in T}: sum{k in W }z[k,t]= 0;

subject to contract{(o,des,r) in Ylt,t in T}:sum{(o,des,o,j) in Yset,dt in Dt[t]}y[o,des,o,j,dt] >= 0.8*LT[o,des,r,t];

subject to contract2{r in R, (i,j) in Alt[r],t in T}:sum{dt in Dt[t]}x[i,j,r,dt]>=0.8*LT[i,j,r,t];

subject to trasnt{(o,des,r) in Ylt,j in Ymid[o,des,r],t in 1..D}: sum{(o,des,i,j) in Yset}y[o,des,i,j,t] - sum{(o,des,j,k) in Yset}y[o,des,j,k,t]=0;

subject to trasnt2{(o,des,r) in Ylt,t in 1..D}: sum{(o,des,o,j) in Yset}y[o,des,o,j,t]-sum{(o,des,i,des) in Yset}y[o,des,i,des,t]=0;
