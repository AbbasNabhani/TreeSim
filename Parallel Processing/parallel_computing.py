# -*- coding: utf-8 -*-
"""
Created on Sat Jan  8 19:23:21 2022

@author: Abbas
"""

import os  
from multiprocessing import Pool  
import time



def run_process(process):  
    os.system('python {}'.format(process)) 

 


if __name__ == "__main__":
    processes = ['Main11.py','Main20.py']
    starttime = time.time()
    pool = Pool(len(processes))
    results = pool.map(run_process,processes)
    pool.close()
    pool.join()
    endtime = time.time()
    print(f"Time taken {endtime-starttime} seconds")
    
    
    



  
