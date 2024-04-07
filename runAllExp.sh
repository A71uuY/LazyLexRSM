#!/bin/bash

#require argument
if [ ! -n "$1" ]; then 
  echo "ERROR: argument required (-full, -fast)" ; exit 1
fi

#reject undefined argument 
if [ $1 != "-full" ] && [ $1 != "-fast" ]; then 
  echo "ERROR: undefined argument (use -full, -fast)" ; exit 1
fi

#create backup of result folder
if [ -e results ]; then
  mv results results_`date +"%H:%M:%S"` 
fi
mkdir results

#main script
echo [`date +"%H:%M:%S"`] experiment started

for i in {0..3}; do
./compile.sh ${i}

for benchSet in "ForExperiments" "probAssignAndWhile" "probloops" "counterex"; do
	for file in examples/${benchSet}/*; do
		#exception for the -fast option
		if [ $1 = "-fast" ] && [ ${i} = 3 ] && [ $file = "examples/probloops/complex.prob" ]; then
			echo [`date +"%H:%M:%S"`] -fast option is used, skipping "$file"... 
			continue
		fi
		
		#default process
	 	echo [`date +"%H:%M:%S"`] started verifying "$file"... 
		echo "#####Beginning of the log for $file#####" >> results/Output_${benchSet}_alg${i}
		echo "" >> results/Output_${benchSet}_alg${i}
		./alg${i}.out < "$file" >> results/Output_${benchSet}_alg${i}
		echo "" >> results/Output_${benchSet}_alg${i}
		echo "#####End of the log for $file#####" >> results/Output_${benchSet}_alg${i}
		echo "" >> results/Output_${benchSet}_alg${i}
		echo "" >> results/Output_${benchSet}_alg${i}
	done
done
done

rm clone1.log
rm clone2.log
echo [`date +"%H:%M:%S"`] experiment finished

#generage result tables
python3 CollectResult.py
