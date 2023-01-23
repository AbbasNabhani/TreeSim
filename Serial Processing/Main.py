# %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%      set trace for debugging     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%##
#import pdb; pdb.set_trace()
# %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%##

###############################################################################################################################################
__author__ = "Abbas Nabhani && Hanne Kathrine Sjolie"                                                                                       ###
__created_on__ = "Sat Apr  4 18:22:00 2020"                                                                                                 ###                                                                                               
__email__ = "forsim@inn.no"                                                                                                                 ###
__status__ = "Development of distance-independent individual tree simulator"                                                                ###
__version__ = "v0.1.0"                                                                                                                      ###                                                                                                             
output_type = "Growth & yield curve"                                                                                                        ###
### Last Edit: 07 May 2022                                                                                                                  ###
###############################################################################################################################################


                                                # %%%%% Choose a site index  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%##
#__SI__ = int(input("Enter the site index(SI): "))
#
#SiteIndex_list = [6, 7, 8, 11, 12, 14, 17, 20, 23, 26]
#while __SI__ not in SiteIndex_list:
#    print("The SI you have entered is not valid. The SI can be one of the numbers of 6, 7, 8, 11, 12, 14, 17, 20, 23, 26")
#    __SI__ = int(input("Re-enter the correct site index(SI): "))

#__SI__ = 6
#__SI__ = 7
#__SI__ = 8
#__SI__ = 11
#__SI__ = 12
#__SI__ = 14
#__SI__ = 17
__SI__ = 20
#__SI__ = 23
#__SI__ = 26

                                                # %%%%% individual tree main module   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%##

import copy
import os
import argparse
import sys
import time
import locale
import csv
from tqdm import tqdm
locale.setlocale(locale.LC_ALL, '')
import matplotlib.pyplot as plt
import time
#import collections
from collections import defaultdict
import importlib 
import simulation
import Tree_Models
import Plot_Models
import pandas as pd
import numpy as np
from operator import itemgetter
   
   
def current_working_directory(directory):
    if(os.path.exists(directory)):
        os.chdir(directory)
        cwd = os.getcwd()
    return cwd

def mkdir(name):
    if not os.path.exists(name):
        os.mkdir(name)
    assert os.path.isdir(name) 
    
# from simulation import Data, tree, plot, Management_prescription, Simulator 
# from Plot_Models import Spruce, Pine,ROS,Birch,Other_broadleaves
# from Tree_Models import GrowthModel

SiteIndex_list = [6, 7, 8, 11, 12, 14, 17, 20, 23, 26]
spruce_species = (1,2,3)
scots_pine_species =(10,11,12,20,21,29)
birch_species=(30,31)
other_broadleaves_species=(50,51,54,59)
ROS_species= (32,52,53,56)
warm_species = (40,41,42,43,44,48,49,55,57,58,65,70)

# Read data input and Generate Sequence Dictionary
full_path = os.path.realpath(__file__)
directory = os.path.dirname(full_path)

jobDirectory = os.path.join(current_working_directory(directory), "Input/")

plotData ='Individual_tree_ simulator.pl'
treeData = 'Individual_tree_ simulator.tr'
suffix='.csv'
# creates the new directory to store the results
mkdir("outputs")  
mkdir("Tree_Simulated_Data")

filename1 = jobDirectory + plotData + suffix
filename2 = jobDirectory + treeData + suffix

plots= defaultdict(dict)
trees= defaultdict(dict)
plots_list = []

with open(filename1) as f:
    next(f)
    reader = csv.reader(f, delimiter=',')
    for row in reader:
        plot_id = row[0]
        SI_spp= int(float(row[14]))
        SI_m= int(float(row[15]))
        stand_age_years= float(row[17])
#        if stand_age_years == 75.0:
        plots[plot_id] = SI_m
        plots_list.append(plot_id)
        

with open(filename2) as f:
    next(f)
    reader =csv.reader(f,delimiter=',')
    for row in reader:
        plot_id = row[0]
        tree_id = int(float(row[1]))
        tree_sp = int(float(row[2]))
        trees[plot_id][tree_id] = tree_sp

""" Mic type  """     
##*******************************************************************************        
Mic_spruce = ["High_spruce", "Medium_spruce" , "Low_spruce"]
Mic_pine = ["High_pine", "Medium_pine"]
Mic_brodleaf = ["broadleaf", "No_man"]    

##*******************************************************************************
"""  Harvest age   
if __SI__ == 26:              
    harvest_periods = [40, 60, 80, 100, 120, 140, 160]
elif __SI__ == 23:
    harvest_periods = [45, 65, 85, 105, 125, 145]
elif __SI__ == 20:
    harvest_periods = [50, 70, 90, 110, 130, 150]
elif __SI__ == 17:
    harvest_periods = [60, 80, 100, 120, 140, 160]
elif __SI__ == 14:
    harvest_periods = [70, 90, 110, 130, 150] 
elif __SI__ == 11 or __SI__ == 12:
    harvest_periods = [80, 100, 120, 140, 160]
elif __SI__ == 8:
    harvest_periods = [85, 105, 125, 145]
elif __SI__ == 7:
    harvest_periods = [90, 110, 130, 150]
else:
    harvest_periods = [95, 115, 135, 155]
"""            
##*******************************************************************************  
"""  Generating Scenarios """          
if (__SI__ >= 15.5):
    scenarios = [x for x in range(1,14)]
    
elif (__SI__ < 15.5) and (__SI__ >= 10.5):
    scenarios = [x for x in range(1,14)]
else:
    scenarios = [x for x in range(1,10)] 
     
##*******************************************************************************     
  
for x in tqdm(plots.keys()):  
    if plots[x] == __SI__:
        print(x)        
        for scenario in scenarios:
            uniqueNO = 0
            if (__SI__ >= 15.5)  and scenario in [1,2,3]:
                MIC_type = Mic_pine[0]
                if __SI__ == 26:              
                    harvest_periods = [40, 100, 160]#, 60, 120, 140, 80]
                elif __SI__ == 23:
                    harvest_periods = [45, 105, 145]#, 65, 125, 85]
                elif __SI__ == 20:
                    harvest_periods = [50, 110, 150]#, 70, 130, 90]
                elif __SI__ == 17:
                    harvest_periods = [60, 120, 160]#, 80, 140, 100]
                
            elif  ((__SI__ < 15.5) and (__SI__ >= 10.5)) and scenario in [1,2,3]:
                MIC_type = Mic_pine[0]
                if __SI__ == 14:
                    harvest_periods = [70, 110, 150]#, 130, 90] 
                elif __SI__ == 11 or __SI__ == 12:
                    harvest_periods = [80, 120, 160]#, 140, 100]
                
            elif (__SI__ >= 15.5)  and scenario in [4,5]: 
                MIC_type = Mic_pine[1]
                if __SI__ == 26:              
                    harvest_periods = [40, 100, 160]#, 60, 120, 140, 80]
                elif __SI__ == 23:
                    harvest_periods = [45, 85, 145]#, 65, 125, 105]
                elif __SI__ == 20:
                    harvest_periods = [50, 90, 150]#, 70, 130, 110]
                elif __SI__ == 17:
                    harvest_periods = [60, 100, 160]#, 120, 140, 80]
            
            elif ((__SI__ < 15.5) and (__SI__ >= 10.5)) and scenario in [4,5]: 
                MIC_type = Mic_pine[1]
                if __SI__ == 14:
                    harvest_periods = [70, 110, 150]#, 130, 90] 
                elif __SI__ == 11 or __SI__ == 12:
                    harvest_periods = [80, 120, 160]#, 140, 100]
                
            elif (__SI__ >= 15.5) and scenario in [6,7,8]:   
                MIC_type = Mic_spruce[0]
                if __SI__ == 26:              
                    harvest_periods = [40, 100, 160]#, 60, 120, 140, 80]
                elif __SI__ == 23:
                    harvest_periods = [45, 105, 145]#, 65, 125, 85]
                elif __SI__ == 20:
                    harvest_periods = [50, 90, 150]#, 70, 130, 110]
                elif __SI__ == 17:
                    harvest_periods = [60, 100, 160]#, 120, 140, 80]

            elif ((__SI__ < 15.5) and (__SI__ >= 10.5)) and scenario in [6,7,8]:   
                MIC_type = Mic_spruce[0]
                if __SI__ == 14:
                    harvest_periods = [70, 110, 150]#, 130, 90] 
                elif __SI__ == 11 or __SI__ == 12:
                    harvest_periods = [80, 120, 160]#, 140, 100]
                
            elif (__SI__ >= 15.5) and scenario in [9,10]: 
                MIC_type = Mic_spruce[1]
                if __SI__ == 26:              
                    harvest_periods = [40, 100, 160]#, 60, 120, 140, 80]
                elif __SI__ == 23:
                    harvest_periods = [45, 85, 145]#, 105, 125, 65]
                elif __SI__ == 20:
                    harvest_periods = [50, 90, 150]#, 110, 130, 70]
                elif __SI__ == 17:
                    harvest_periods = [60, 100, 160]#, 120, 140, 80]
                
            elif ((__SI__ < 15.5) and (__SI__ >= 10.5)) and scenario in [9,10]: 
                MIC_type = Mic_spruce[1]
                if __SI__ == 14:
                    harvest_periods = [70, 110, 150]#, 130, 90] 
                elif __SI__ == 11 or __SI__ == 12:
                    harvest_periods = [80, 120, 160]#, 140, 100]
                
            elif (__SI__ >= 15.5)  and scenario == 11: 
                MIC_type = Mic_spruce[2]
                if __SI__ == 26:              
                    harvest_periods = [40, 100, 160]#, 60, 120, 140, 80]
                elif __SI__ == 23:
                    harvest_periods = [45, 85, 145]#, 105, 125, 65]
                elif __SI__ == 20:
                    harvest_periods = [50, 90, 150]#, 110, 130, 70]
                elif __SI__ == 17:
                    harvest_periods = [60, 100, 160]#, 80, 140, 120]
                
            elif ((__SI__ < 15.5) and (__SI__ >= 10.5)) and scenario == 11: 
                MIC_type = Mic_spruce[2]
                if __SI__ == 14:
                    harvest_periods = [70, 110, 150]#, 130, 90] 
                elif __SI__ == 11 or __SI__ == 12:
                    harvest_periods = [80, 120, 160]#, 140, 100]
            
            elif (__SI__ >= 15.5) and scenario == 12:         
                MIC_type = Mic_brodleaf[0]
                if __SI__ == 26:              
                    harvest_periods = [40, 100, 160]#, 60, 120, 140, 80]
                elif __SI__ == 23:
                    harvest_periods = [45, 85, 145]#, 105, 125, 65]
                elif __SI__ == 20:
                    harvest_periods = [50, 70, 90]#, 110, 130, 150]
                elif __SI__ == 17:
                    harvest_periods = [60, 100, 160]#, 120, 140, 80]

            elif ((__SI__ < 15.5) and (__SI__ >= 10.5)) and scenario == 12:         
                MIC_type = Mic_brodleaf[0]
                if __SI__ == 14:
                    harvest_periods = [70, 110, 150]#, 130, 90] 
                elif __SI__ == 11 or __SI__ == 12:
                    harvest_periods = [80, 120, 160]#, 140, 100]
                
            elif (__SI__ >= 15.5) and scenario == 13:         
                MIC_type = Mic_brodleaf[1]
                if __SI__ == 26:              
                    harvest_periods = [40, 100, 160]#, 60, 120, 140, 80]
                elif __SI__ == 23:
                    harvest_periods = [45, 85, 145]#, 105, 125, 65]
                elif __SI__ == 20:
                    harvest_periods = [50, 90, 150]#, 110, 130, 70]
                elif __SI__ == 17:
                    harvest_periods = [60, 100, 160]#, 120, 140, 80]
            
            elif ((__SI__ < 15.5) and (__SI__ >= 10.5)) and scenario == 13:         
                MIC_type = Mic_brodleaf[1] 
                if __SI__ == 14:
                    harvest_periods = [70, 110, 150]#, 130, 90] 
                elif __SI__ == 11 or __SI__ == 12:
                    harvest_periods = [80, 120, 160]#, 140, 100]
                
            elif (__SI__ < 10.5) and scenario in [1,2]:
                MIC_type = Mic_pine[0]
                if __SI__ == 8:
                    harvest_periods = [85, 105, 145]#, 125]
                elif __SI__ == 7:
                    harvest_periods = [90, 110, 150]#, 130]
                else:
                    harvest_periods = [95, 115, 155]#, 135] 
                
            elif (__SI__ < 10.5) and scenario == 3:
                MIC_type = Mic_pine[1]
                if __SI__ == 8:
                    harvest_periods = [85, 105, 145]#, 125]
                elif __SI__ == 7:
                    harvest_periods = [90, 110, 150]#, 130]
                else:
                    harvest_periods = [95, 115, 155]#, 135] 
                
            elif (__SI__ < 10.5) and scenario in [4,5]:
                MIC_type = Mic_spruce[0]
                if __SI__ == 8:
                    harvest_periods = [85, 105, 145]#, 125]
                elif __SI__ == 7:
                    harvest_periods = [90, 110, 150]#, 130]
                else:
                    harvest_periods = [95, 115, 155]#, 135] 
                
            elif (__SI__ < 10.5) and scenario == 6:
                MIC_type = Mic_spruce[1]
                if __SI__ == 8:
                    harvest_periods = [85, 105, 145]#, 125]
                elif __SI__ == 7:
                    harvest_periods = [90, 110, 150]#, 130]
                else:
                    harvest_periods = [95, 115, 155]#, 135] 
                
            elif (__SI__ < 10.5) and scenario == 7:
                MIC_type = Mic_spruce[2]
                if __SI__ == 8:
                    harvest_periods = [85, 105, 145]#, 125]
                elif __SI__ == 7:
                    harvest_periods = [90, 110, 150]#, 130]
                else:
                    harvest_periods = [95, 115, 155]#, 135] 
                
            elif (__SI__ < 10.5) and scenario == 8:
                MIC_type = Mic_brodleaf[0]
                if __SI__ == 8:
                    harvest_periods = [85, 105, 145]#, 125]
                elif __SI__ == 7:
                    harvest_periods = [90, 110, 150]#, 130]
                else:
                    harvest_periods = [95, 115, 155]#, 135] 
                
            elif (__SI__ < 10.5) and scenario == 9:
                MIC_type = Mic_brodleaf[1] 
                if __SI__ == 8:
                    harvest_periods = [85, 105, 145]#, 125]
                elif __SI__ == 7:
                    harvest_periods = [90, 110, 150]#, 130]
                else:
                    harvest_periods = [95, 115, 155]#, 135] 
            
            if MIC_type == Mic_brodleaf[1]: # we don't harvest
                harvest_periods = [50]

            
            for Each_period in harvest_periods:
                uniqueNO += 1 
                print("scenario is:",str(scenario) + str(uniqueNO)) 
                   
                if __name__ == "__main__":
                    
                    importlib.reload(simulation)
                    importlib.reload(Tree_Models)
                    importlib.reload(Plot_Models)
                    
                    parser = argparse.ArgumentParser()
                    parser.add_argument("-f", dest= "jobDir", nargs= "+", metavar = "str", help="Working Directory for the job")
    
                    start = time.time()        
#                    args = parser.parse_args()   
                    jobDirectory = current_working_directory(directory)
                    if not os.path.isdir(jobDirectory):
                        print("ERROR: Directory %s not found."%(jobDirectory))
                        sys.exit(1)
                    start = time.time()        
                    prob = simulation.Data(jobDirectory)
                    prob2= copy.deepcopy(prob)
                    if len(prob2.plots[x].treeList) != 0:
                        
                        plot = Plot_Models.Species(Data= prob2, year = prob2.plots[x].year,plot_id = prob2.plots[x].plot_id, t=prob2.plots[x].stand_age_years, H40 =prob2.plots[x].SI_m, N=prob2.plots[x].N_tree_ha,
                                                treeList=prob2.plots[x].treeList, Latitude=prob2.plots[x].Latitude, Region=prob2.plots[x].region, Altitude=prob2.plots[x].altitude_m, subplot_size = prob2.plots[x].subplot_size, mortality = True)
                                           
                                                  
                        simrun = simulation.Simulator(plot = plot,jobDir= jobDirectory, scenario = scenario, Harvest_age = Each_period , MIC_TYPE = MIC_type, unique = uniqueNO,  YearN = True, Data= prob2)
                            
                        with open(current_working_directory(directory) +'/Tree_Simulated_Data/'+ str(x) +"_scenario" + str(scenario) + str(uniqueNO) + '_tree_simulation.csv', 'w', newline='') as csvfile:
                            fieldnames = ["plot_id",'tree_id','tree_sp','dbh','height', 'diameter_class','tree_Factor', 'SI_spp', 'SI_m', 'n_tree', 'species','Period', 'coord_x', 'coord_y',  'year', 'volsum', 'vol_spruce', 'vol_pine','vol_birch', 'vol_others', 'vol_ROS', 'vol_warm', 'management']
                            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                            writer.writeheader()
    
                            dict_keys = [{k: v.keys()} for k,v in Tree_Models.GrowthModel.TITLES.items()]
                            
                            for t in dict_keys:
                                for i in t.keys():
                                    for periods in t.values():
                                        for j in periods:   
                                            writer.writerow({"plot_id": Tree_Models.GrowthModel.TITLES[i][j].plot_id, 'tree_id': Tree_Models.GrowthModel.TITLES[i][j].tree_id, 'tree_sp':Tree_Models.GrowthModel.TITLES[i][j].tree_sp,'dbh':Tree_Models.GrowthModel.TITLES[i][j].dbh, 
                                              'height':Tree_Models.GrowthModel.TITLES[i][j].height,'diameter_class': Tree_Models.GrowthModel.TITLES[i][j].diameter_class,'tree_Factor': Tree_Models.GrowthModel.TITLES[i][j].tree_Factor,'SI_spp': Tree_Models.GrowthModel.TITLES[i][j].SI_spp,
                                              'SI_m': Tree_Models.GrowthModel.TITLES[i][j].SI_m , 'n_tree':Tree_Models.GrowthModel.TITLES[i][j].n_tree,'species': Tree_Models.GrowthModel.TITLES[i][j].species,'Period': Tree_Models.GrowthModel.TITLES[i][j].Period,'coord_x': Tree_Models.GrowthModel.TITLES[i][j].coord_x,
                                              'coord_y': Tree_Models.GrowthModel.TITLES[i][j].coord_y, 'year': Tree_Models.GrowthModel.TITLES[i][j].year, 'volsum': Tree_Models.GrowthModel.TITLES[i][j].volsum, 'vol_spruce': Tree_Models.GrowthModel.TITLES[i][j].vol_spruce, 'vol_pine': Tree_Models.GrowthModel.TITLES[i][j].vol_pine,
                                              'vol_birch': Tree_Models.GrowthModel.TITLES[i][j].vol_birch, 'vol_others': Tree_Models.GrowthModel.TITLES[i][j].vol_others, 'vol_ROS': Tree_Models.GrowthModel.TITLES[i][j].vol_ROS, 'vol_warm': Tree_Models.GrowthModel.TITLES[i][j].vol_warm, 'management':Tree_Models.GrowthModel.TITLES[i][j].management})   
                            

                    else:
                        #print("\n\n\nThere is no tree in this plot.\n")
                        
                        with open(filename2, 'a', newline='') as csvfile:
                            fieldnames = ['plot_id','tree_id','tree_sp','dbh','mort','height', 'diameter_class','tree_Factor', 'volume', 'Inc','Biomass','SI_spp', 'SI_m', 't_age','volsum','vol_spruce','vol_pine','vol_birch','vol_others','vol_ROS','vol_warm']
                            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                            for i in range(0,len(prob.TITLES)):             
                                writer.writerow({"plot_id": prob.TITLES[i].plot_id, 'tree_id': prob.TITLES[i].tree_id, 'tree_sp':prob.TITLES[i].tree_sp,'dbh':prob.TITLES[i].dbh, 'mort':prob.TITLES[i].mort,
                                                  'height':prob.TITLES[i].height,'diameter_class': prob.TITLES[i].diameter_class,'tree_Factor': prob.TITLES[i].tree_Factor,
                                                  'volume': prob.TITLES[i].volume,'Inc': prob.TITLES[i].Inc,'Biomass': prob.TITLES[i].Biomass,'SI_spp': prob.TITLES[i].SI_spp,
                                                  'SI_m': prob.TITLES[i].SI_m, 't_age': prob.TITLES[i].t_age,'volsum': prob.TITLES[i].volsum,'vol_spruce': prob.TITLES[i].vol_spruce,
                                                  'vol_pine': prob.TITLES[i].vol_pine,'vol_birch': prob.TITLES[i].vol_birch,'vol_others': prob.TITLES[i].vol_others,'vol_ROS': prob.TITLES[i].vol_ROS,
                                                  'vol_warm': prob.TITLES[i].vol_warm})
                         
    



