import csv, copy, os 

#total benchmark count
global TotalBenchCount
TotalBenchCount=0

#success count of each algorithm
global SuccessCount
SuccessCount=[0,0,0,0]

# to store an individual experiment result statistics
class SingleResult(object): 
    def __init__(self) -> None:
        self.prob_name = ""     # benchmark name
        self.total_time = 0     # computation time
        self.n_states = 0       # number of states of pCFG 
        self.n_dim = 0          # dimension of the synthesized LexRSM (if successful)
        self.solved = False     # solution found flag 
        self.finished = False   # computation finished flag
        self.stop_iter = None   # the dimension where the iteration stopped (if unsuccessful)


#scrape the result statistics from the experiment log
def process_file(file_name): 
    f = open(file_name)
    lines = f.readlines()
    results = []
    for line in lines:
        if line.startswith('#####Beginning of '): # the beinning of the log
            cur_result = SingleResult()
            prob_name = line.split('/')[-1].split('.')[0]
            cur_result.prob_name = prob_name
        elif line.startswith('The CFG'): # "The CFG constructed has xx states"
            n_stats = int(line.split()[-2])
            cur_result.n_states = n_stats
        elif line.startswith('Found'): # "Found a solution of dimension x."
            n_dim = int(line.split()[-1].split('.')[0])
            cur_result.solved = True
            cur_result.n_dim = n_dim
        elif line.startswith('Total'): # "Total time taken: xxx"
            tot_time = float(line.split()[-1])
            cur_result.total_time = tot_time
            cur_result.finished = True 
        elif line.startswith('No solution'): # "No solution found, stopped after x iterations"
            cur_result.stop_iter = int(line.split()[-2])
        elif line.startswith('#####End of'): # the end of the log
            results.append(cur_result) 
    #print(len(results))
    return results


result_dict = dict()
result_dict['non-prob'] = dict()
result_dict['prob-loop'] = dict()
result_dict['prob-assign'] = dict()
result_dict['counterex'] = dict()


#alg0 ~ alg3: result statistics scraped by process_file
#type: the type of input program (non-prob, prob-loop, prob-assign, counterex)
#generates a dictionary of result table
def merge_dict_3(alg0,alg1,alg2,alg3,type):
    global TotalBenchCount
    global SuccessCount
    algs = [alg0,alg1,alg2,alg3]
    for alg_num in range (4):
        for result in algs[alg_num]:
            if alg_num == 0: #create a new entry, increment the benchmark count
                result_dict[type][result.prob_name] = [['N/A', 'N/A'],['N/A', 'N/A'],['N/A', 'N/A'],['N/A', 'N/A']] 
                TotalBenchCount += 1
            
            #EXEPTION: alg0 (STR) does not work correctly for the benchmark counterexStr1, leave the data N/A
            if result.prob_name == 'counterexStr1' and alg_num == 0:
                continue

            #add the result to the dict, increment the success count
            if result.finished:
                if result.solved:
                    SuccessCount[alg_num] += 1
                    result_dict[type][result.prob_name][alg_num] = [result.n_dim,result.total_time]
                else:
                    result_dict[type][result.prob_name][alg_num] = ['False',result.total_time]
            else:
                result_dict[type][result.prob_name][alg_num] = ['False','Aborted']

           

#Generate Table 2 (the full experiment result)
def print_file_single_4(res_dict):
    csv_header_0 =['Benchmark Spec.',' ',' ','Synthesis result',' ',' ',' ',' ',' ',' ',' ']
    csv_header_1 =[' ',' ',' ','Baselines',' ',' ',' ','Our Algs',' ',' ',' ']
    csv_header_2 =[' ',' ',' ','STR',' ','LWN',' ','SMC',' ','EMC',' ']
    csv_header_3 =['Model','P.l','P.a','dim.','time','dim.','time','dim.','time','dim.','time']
    csv_header_4 = ['_______________','_____','_____','________________','________','______','________','________','________','_____','________']

    global TotalBenchCount
    global SuccessCount
    csv_header_5 =['Total Benchmark count',TotalBenchCount,' ',' ',' ',' ',' ',' ',' ',' ',' ']
    csv_header_6 =['Success count STR',SuccessCount[0],' ',' ',' ',' ',' ',' ',' ',' ',' '] 
    csv_header_7 =['Success count LWN',SuccessCount[1],' ',' ',' ',' ',' ',' ',' ',' ',' ']
    csv_header_8 =['Success count SMC',SuccessCount[2],' ',' ',' ',' ',' ',' ',' ',' ',' ']
    csv_header_9 =['Success count EMC',SuccessCount[3],' ',' ',' ',' ',' ',' ',' ',' ',' ']
    
    #main
    with open('./result_table/exp-res-samewpaper.csv','w',newline='') as f:
        writer = csv.writer(f)
        #print header
        writer.writerow(csv_header_0)
        writer.writerow(csv_header_1)
        writer.writerow(csv_header_2)
        writer.writerow(csv_header_3)
        writer.writerow(csv_header_4)

        #generate the table row of each behchmark (for 'non-prob', 'prob-loop', 'prob-assign')
        for bm in list(res_dict['non-prob'].keys()): 
            print_single_example(res_dict, writer, bm,'non-prob','long')
            if bm in list(res_dict['prob-loop'].keys()):
                print_single_example(res_dict, writer, bm,'prob-loop','long')
            if bm in list(res_dict['prob-assign'].keys()):
                print_single_example(res_dict, writer, bm,'prob-assign','long')

        #generate the table row of each behchmark (for 'counterex')
        for bm in list(res_dict['counterex'].keys()):
            print_single_example(res_dict, writer, bm,'counterex','long')

        #print footer    
        writer.writerow(csv_header_4)
        writer.writerow(csv_header_5)
        writer.writerow(csv_header_6)
        writer.writerow(csv_header_7)
        writer.writerow(csv_header_8)
        writer.writerow(csv_header_9)
          


#Generate Table 1 (result summary where we observe difference)
def print_file_single_5(res_dict):
    csv_header_1 = ['Benchmark Spec.', ' ', ' ', 'Synthesis result',' ',' ',' ']
    csv_header_2 = [' ', ' ', ' ', 'Baselines', ' ', 'Our algs.',' ']
    csv_header_3 = ['Model', 'P.l', 'P.a', 'STR', 'LWN', 'SMC', 'EMC']
    csv_header_4 = ['___________________','_____','_____','________________','_____','________','___']
    with open('./result_table/table1.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(csv_header_1)
        writer.writerow(csv_header_2)
        writer.writerow(csv_header_3)
        writer.writerow(csv_header_4)
        print_single_example(res_dict, writer,'complex','non-prob','short')
        print_single_example(res_dict, writer,'complex','prob-loop','short')
        print_single_example(res_dict, writer,'complex','prob-assign','short')
        print_single_example(res_dict, writer,'cousot9','non-prob','short')
        print_single_example(res_dict, writer, 'cousot9', 'prob-loop','short')
        print_single_example(res_dict, writer, 'loops', 'non-prob','short')
        print_single_example(res_dict, writer, 'nestedLoop', 'prob-assign','short')
        print_single_example(res_dict, writer, 'realheapsort', 'non-prob','short')
        print_single_example(res_dict, writer, 'realheapsort_step1', 'non-prob','short')
        print_single_example(res_dict, writer, 'realheapsort_step1', 'prob-assign','short')
        print_single_example(res_dict, writer, 'realshellsort', 'prob-assign','short')
        print_single_example(res_dict, writer, 'serpent', 'non-prob','short')
        print_single_example(res_dict, writer, 'speedDis1', 'non-prob','short')
        print_single_example(res_dict, writer, 'speedDis2', 'non-prob','short')
        print_single_example(res_dict, writer, 'speedSimpleMultiple', 'non-prob','short')
        print_single_example(res_dict, writer, 'speedSimpleMultipleDep', 'non-prob','short')
        print_single_example(res_dict, writer, 'speedSingleSingle2', 'prob-assign','short')
        print_single_example(res_dict, writer, 'speedpldi3', 'non-prob','short')
        print_single_example(res_dict, writer, 'speedpldi3', 'prob-loop','short')
        print_single_example(res_dict, writer, 'counterexStr1', 'counterex','short')
        print_single_example(res_dict, writer, 'counterexStr2', 'counterex','short')
        



#print the table row of a specific behchmark
def print_single_example(res_dict, writer, bm, type, length):
    lin = [] #new row

    #add the benchmark spec to lin
    lin.append(bm)
    if type=='non-prob':
        lin.append('False')
        lin.append('False')
    elif type =='prob-loop':
        lin.append('True')
        lin.append('False')
    elif type == 'prob-assign':
        lin.append('True')
        lin.append('True')
    elif type == 'counterex':
        lin.append('False')
        lin.append('True')
    ls = res_dict[type][bm]

    #add the result to lin
    solv = []
    for l in ls:
        solvs = l[0]
        tims = l[1]
        if length == 'long':
            solv += [solvs] + [tims]
        elif length == 'short':
            solv += [solvs]
    lin += solv
    writer.writerow(lin)


results_0 = process_file('./results/Output_ForExperiments_alg0')
results_1 = process_file('./results/Output_ForExperiments_alg1')
results_2 = process_file('./results/Output_ForExperiments_alg2')
results_3 = process_file('./results/Output_ForExperiments_alg3')
merge_dict_3(results_0,results_1,results_2,results_3,'non-prob')

results_0 = process_file('./results/Output_probAssignAndWhile_alg0')
results_1 = process_file('./results/Output_probAssignAndWhile_alg1')
results_2 = process_file('./results/Output_probAssignAndWhile_alg2')
results_3 = process_file('./results/Output_probAssignAndWhile_alg3')
merge_dict_3(results_0,results_1,results_2,results_3,'prob-assign')

results_0 = process_file('./results/Output_probloops_alg0')
results_1 = process_file('./results/Output_probloops_alg1')
results_2 = process_file('./results/Output_probloops_alg2')
results_3 = process_file('./results/Output_probloops_alg3')
merge_dict_3(results_0,results_1,results_2,results_3,'prob-loop')

results_0 = process_file('./results/Output_counterex_alg0')
results_1 = process_file('./results/Output_counterex_alg1')
results_2 = process_file('./results/Output_counterex_alg2')
results_3 = process_file('./results/Output_counterex_alg3')
merge_dict_3(results_0,results_1,results_2,results_3,'counterex')

if not os.path.exists("result_table"):
    os.makedirs("result_table")

print_file_single_4(result_dict)
print_file_single_5(result_dict)


