import pandas as pd
import os
import re

def foo2():
    print("a")

def foo():
    print("kun")


def get_csv(current_dir):
    csv_re = re.compile("(.*.csv)$")
    for root, dirs, files in os.walk(current_dir + "/results"):
        for file in files:
            if csv_re.match(file):
                csv = pd.read_csv(current_dir + "/results/" + file, sep="\t")
                return csv
            

def all_same_length(a_dict):
    it = iter(list(a_dict.values()))
    the_len = len(next(it))
    if not all(len(alist) == the_len for alist in it):
        return False
    return True

def get_benchmark_set_name(row):
    bench_path = row['tool']
    benchmarkname_re = re.compile("^([^/]*)/.*smt2$")
    benchmark_match = benchmarkname_re.match(bench_path)
    if benchmark_match:
        return benchmark_match.group(1)
    assert(False)


def get_data(csv):
    """
        Creates dict {benchmark_set : {benchmark_file : [--list of names of benchmak files], 
                                        cpu_time : [--list of times of cpu--],
                                        walltime : [--]list of wall times--],
                                        memory : [--list of memory consumptions--]}}
    """
    benchmark_data = {}
    
    for num, row in csv.iterrows():
        if num <= 1:
            continue
        benchmark_set_name = get_benchmark_set_name(row)
        
        if benchmark_set_name not in benchmark_data:
            header = {
                "benchmarkfile" : [],
                "result" : [],
                "cputime" : [],
                "walltime" : [],
                "memory" : []
            }
            benchmark_data[benchmark_set_name] = header
        
        benchmark_data[benchmark_set_name]["benchmarkfile"].append(row["tool"])
        benchmark_data[benchmark_set_name]["result"].append(row["q3b Q3B version 1.1-dev"])
        benchmark_data[benchmark_set_name]["cputime"].append(float(row["q3b Q3B version 1.1-dev.1"]))
        benchmark_data[benchmark_set_name]["walltime"].append(float(row["q3b Q3B version 1.1-dev.2"]))
        benchmark_data[benchmark_set_name]["memory"].append(row["q3b Q3B version 1.1-dev.3"])
        assert(all_same_length(benchmark_data[benchmark_set_name]))
    
    
    return benchmark_data
        
       
def dict_to_df(bench_data):
    """
        Creates dict {benchmark_set : dataframe}
    """
    
    return dict(map(lambda item: (item[0], pd.DataFrame(data = item[1])), bench_data.items()))

def sum_data(benchmark_data):
    sumdata = {}
    for benchmark_set, bench_df in benchmark_data.items():
        header = {
            "total" : len(bench_df),
            "unsat" : len(get_df(bench_df, "false")),
            "sat" : len(get_df(bench_df, "true")),
            "solved" : len(get_df(bench_df, "true")) + len(get_df(bench_df, "false")),
            "timeout" : len(get_df(bench_df, "TIMEOUT")),
            "segfault" : len(get_df(bench_df, "SEGFAULT")),
            "other" : len(get_df(bench_df, "others"))
        }
        #print(bench_df.result)
        sumdata[benchmark_set] = header
    return pd.DataFrame(data = sumdata)
        


def get_count(df):
    return 1 if len(df) == 0 else len(df)

def get_df(bench_df, result):
    if result == "others":
        return bench_df[(bench_df.result != "TIMEOUT") & (bench_df.result != "true")  & (bench_df.result != "false") & (bench_df.result != "SEGFAULT")]
        
    return bench_df[bench_df.result == result]

def time_data(benchmark_data):
    sumdata = {}
    for benchmark_set, bench_df in benchmark_data.items():
        sat_df = get_df(bench_df, "true")
        unsat_df = get_df(bench_df, "false")
        timeout_df = get_df(bench_df, "TIMEOUT")
        segfault_df = get_df(bench_df, "SEGFAULT")
        others_df = get_df(bench_df, "others")
        
        
        header = {
            "total" : bench_df['cputime'].sum(),
            
            "sat total" : sat_df['cputime'].sum(),
            "unsat total" : unsat_df['cputime'].sum(),
            "timeout total" : timeout_df['cputime'].sum(),
            "segfault total" : segfault_df['cputime'].sum(), 
            "other total" : others_df['cputime'].sum(),
            "average" : bench_df['cputime'].sum() / len(bench_df) ,
            "sat average" : sat_df['cputime'].sum() / get_count(sat_df) ,
            "unsat average" : unsat_df['cputime'].sum() / get_count(unsat_df) ,
            "timeout average" : timeout_df['cputime'].sum() / get_count(timeout_df) ,
            "segfault average" : segfault_df['cputime'].sum() / get_count(segfault_df) ,
            "others average" : others_df['cputime'].sum() / get_count(others_df) ,
        }
        sumdata[benchmark_set] = header
        
    return pd.DataFrame(sumdata)


def highlight(row, c1, c2):
    bckg = 'background-color'
    w = 'white'

    background = []
    i = 0
    while (i < len(row) - 1):
        if row.iloc[i] < row.iloc[i + 1]:
            background.append(f'{bckg}: {c1}')
            background.append(f'{bckg}: {c1}')
        elif row.iloc[i] > row.iloc[i + 1]:
            background.append(f'{bckg}: {c2}')
            background.append(f'{bckg}: {c2}')
        else:
            background.append(f'{bckg}: {w}')
            background.append(f'{bckg}: {w}')
        i += 2

    return background

def highlight_greater(row):
    return highlight(row, 'lightblue', 'pink')

def highlight_smaller(row):
    return highlight(row, 'pink', 'lightblue')

    
def is_error(result):
    non_error = ['false', 'true', 'TIMEOUT']
    return not(result in non_error)
    
def is_mistake(orig_res, new_res):
    if orig_res == "true" and new_res == "false":
        return True
    if orig_res == "false" and new_res == "true":
        return True
    return False
    
    
def append_dfs(alist, orig_df, new_df, name):
    # filters orig and new to be only with particular name and adds it as a tuple to alist
    filt_orig = orig_df[orig_df['benchmarkfile'] == name]
    filt_new = new_df[new_df['benchmarkfile'] == name]
    alist.append((filt_orig, filt_new))
    
    
def get_worse_results(orig_path, new_path):
    orig_df = dict_to_df(get_data(get_csv(orig_path)))
    new_df = dict_to_df(get_data(get_csv(new_path)))
    new_errors = []
    both_errors = []
    removed_errors = []
    new_timeouts = []
    removed_timeouts = []
    nan_values = []
    mistakes = []
    for key in orig_df.keys():
        assert(len(orig_df[key]) == len(new_df[key]))
        
        for ind in orig_df[key].index:
            
            
            new_match = new_df[key].loc[(new_df[key]['benchmarkfile'] == str(orig_df[key]['benchmarkfile'][ind])) ]
            #print(f"New match = {new_match}, type= {type(new_match)} {new_match['benchmarkfile']}")
            for new_ind in new_match.index:
                if orig_df[key]['result'][ind] != new_match['result'][new_ind]:
                    
                                       
                    if pd.isna(orig_df[key]['result'][ind]):
                        assert(pd.isna(new_match['result'][new_ind]))
                        append_dfs(nan_values,orig_df[key], new_match, name= orig_df[key]['benchmarkfile'][ind])
                    elif is_error(new_match['result'][new_ind]) and not is_error(orig_df[key]['result'][ind]):
                        
                        append_dfs(new_errors,orig_df[key], new_match, name= orig_df[key]['benchmarkfile'][ind])
                        
                    elif not is_error(new_match['result'][new_ind]) and is_error(orig_df[key]['result'][ind]):
                        
                        
                        append_dfs(removed_errors,orig_df[key], new_match, name= orig_df[key]['benchmarkfile'][ind])
                    
                    elif is_error(new_match['result'][new_ind]) and is_error(orig_df[key]['result'][ind]):
                        
                        append_dfs(both_errors,orig_df[key], new_match, name= orig_df[key]['benchmarkfile'][ind])
                        # works only if they are different errors (it's stupid)
                        
                    elif new_match['result'][new_ind] == 'TIMEOUT' and orig_df[key]['result'][ind] != 'TIMEOUT':
                        
                        
                        append_dfs(new_timeouts,orig_df[key], new_match, name= orig_df[key]['benchmarkfile'][ind])
                        
                    elif new_match['result'][new_ind] != 'TIMEOUT' and orig_df[key]['result'][ind] == 'TIMEOUT':
                        
                        append_dfs(removed_timeouts,orig_df[key], new_match, name= orig_df[key]['benchmarkfile'][ind])
                        
                    elif is_mistake(orig_df[key]['result'][ind], new_match['result'][new_ind]):
                        
                        append_dfs(mistakes,orig_df[key], new_match, name= orig_df[key]['benchmarkfile'][ind])
                        
    
                    else:
                        print(f"New {new_match['result'][new_ind]}")
                        print(f"Old {orig_df[key]['result'][ind]}")
                        assert(False)
    return new_errors, both_errors, removed_errors, new_timeouts, removed_timeouts,nan_values, mistakes

def create_sum_time_comparison(path, name):
    csv = get_csv(path)
    df = dict_to_df(get_data(csv))
    sumdata = sum_data(df)
    timedata = time_data(df)
    sumdata = sumdata.reindex(sorted(sumdata.columns), axis=1)
    timedata = timedata.reindex(sorted(timedata.columns), axis=1)
    return sumdata, timedata
    
def copmare_dfs(path1, name1,path2, name2):
    sumdata1, timedata1 = create_sum_time_comparison(path1, name1)
    sumdata2, timedata2 = create_sum_time_comparison(path2, name2)
    sum_comparison = sumdata1.compare(sumdata2, align_axis=1, keep_shape=True, keep_equal=True, result_names = (name1, name2))
    time_comparison = timedata1.compare(timedata2,align_axis=1, keep_shape=True, keep_equal=True, result_names = (name1, name2))
    sum_comparison = sum_comparison.style.apply(highlight_greater, axis=1)
    time_comparison = time_comparison.style.apply(highlight_smaller, axis=1)
    return sum_comparison,time_comparison
    
