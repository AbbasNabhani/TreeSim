###############################################################################################################################################
__author__ = "Abbas Nabhani && Hanne Kathrine Sjolie"                                                                                       ###
__created_on__ = "Sat Apr  4 18:22:00 2020"                                                                                                 ###                                                                                               
__email__ = "forsim@inn.no"                                                                                                                 ###
__status__ = "Development of distance-independent individual tree simulator"                                                                ###
__version__ = "v0.1.0"                                                                                                                      ###                                                                                                                                                                                                                              
output_type = "3D visualization and animation of the simulated results"                                                                     ###
### Last Edit: 07 May 2022                                                                                                                  ###
###############################################################################################################################################


import csv, json #imports needed libraries for conversion
import os

def current_working_directory(directory):
    if(os.path.exists(directory)):
        os.chdir(directory)
        cwd = os.getcwd()
    return cwd

full_path = os.path.realpath(__file__)   
directory = os.path.dirname(full_path)


with open(current_working_directory(directory)+'/A94962_scenario21_tree_simulation.csv') as f: 
    reader = csv.DictReader(f)
    rows = list(reader)  

with open(current_working_directory(directory)+'/A94962_scenario21_tree_simulation.json', 'w') as n: 
    json.dump(rows, n) 
