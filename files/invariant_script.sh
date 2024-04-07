./files/aspicV3.4 files/aspic.fast > files/InvariantOutput
awk 'BEGIN {x=0} x==1{print} /^\*\*\* Results :/{x=1}' < files/InvariantOutput > InvariantOutput.tmp
mv InvariantOutput.tmp files/InvariantOutput
rm aspic.log