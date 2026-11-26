from engine import *
from fractions import Fraction as Fr
import sys
S=System(0,1,3)
for den in [50,100,200,1000,10**4]:
    u=Fr(1,den); y=(1-u)/2
    for rounds,maxwin,sh in [(8,3000,(-2,-1,0,1,2)),(16,20000,(-3,-2,-1,0,1,2,3))]:
        pr=Prover(S,(1,u,y),maxwin=maxwin,rounds=rounds,shifts=sh); r,Bg,dep=pr.run()
        print(den,rounds,r,Bg,len(pr.W),flush=True)
