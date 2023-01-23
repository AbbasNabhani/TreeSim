# -*- coding: utf-8 -*-
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

                                                # %%%%%%      Choose a site index      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%##
"""The number of 5-year intervals """                                                                                                       
steps = 40                                                                                                                                   
interval = 5                                                                                                                                


                                                
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

                                                # %%%%%           Simulation          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%##

"""
             simulation
========================================
This module contains five classes: Class Data to read the forest inventory data (NFI), store them in two different classes; 
one tree class for storing the tree level data into each object called tree and the other one, plot class 
for storing plot level data into each object called plot.
Another class to specify forest management prescriptions
and simulator class to simulate stand tables based on individual tree growth models.

========================================

"""
from math import log, sqrt, exp,pi, gamma
import numpy as np
import copy
import os, sys, random
import csv
import locale
locale.setlocale(locale.LC_ALL, '')
import math
import matplotlib.pyplot as plt
from tools.tabulate import *
from itertools import islice
from collections import defaultdict
from tqdm import tqdm
import operator
import seaborn as sns
import matplotlib.gridspec as gridspec
import pylab as pl
import time
from matplotlib.pyplot import figure
import json
from heapq import nlargest
from operator import itemgetter
from django.utils.crypto import get_random_string
import titles_NewTree

INDENT = '---->'

import warnings
#suppress warnings
warnings.filterwarnings('ignore')

## disable "SettingWithCopyWarning" warning 
import pandas as pd
pd.options.mode.chained_assignment = None  # default='warn'
#******************************* for x and y of tree location
np.random.seed(1)

                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class Data():
    """ 
    Class with the parameters that define the instance of the problem
    Objective: Manage instance of problem
    Required Methods:
      - Reading
      - Print Results
      - Save Results
    Mandatory Variables:
      - Input file
      - Name of the instance
      """
#    heights= {}
    def __init__(self,jobDir):
        self.jobDir = jobDir
        self.input = os.path.join(jobDir,'Input')
        self.output = os.path.join(jobDir,'outputs')
        self.name = os.path.basename(self.jobDir)
        

        self.TITLES = []
        self.id_list=list()  
        self.plotId_plotlevel=list()
        self.treeFactor_Dict=dict()
        self.subplot_sizeDict = dict()
        self.LatDict=dict()
        self.LongDict=dict()
        self.AltDict = dict()
        self.GridDict=dict()
        self.years = dict()
        self.SI_mDict=dict()
        self.SI_sppDict= dict()
        self.weatherDict= dict()      #this dict is filled with municipality id data
        self.weatherErrorDict= dict() #this dict is filled with county id data
        self.weatherReferenceTime= dict()
        self.treeDict= defaultdict(list)
        self.plotData = os.path.join(self.input,'Individual_tree_ simulator.pl.csv')
        self.treeData = os.path.join(self.input, 'Individual_tree_ simulator.tr.csv')
        self.factors= os.path.join(self.input, 'Individual_tree_ simulator.levels.csv')
        self.weatherData = os.path.join(self.input, 'Individual_tree_ simulator.MeanAnnualTemp.csv')
        self.ageData = os.path.join(self.input, 'Individual_tree_ simulator.age.csv')

       
        self.plots = {}
        self.trees={}
        self.gridsize_x = 20
        self.gridsize_y = 20
        self.readweatherData()
        #self.readTree_age_Data()
        self.readplotData()
        self.readtreeData()
        self.VariableBuilder()


        
                                                    # %%%%%%     Finds the mean height of the two thickest trees in each plot
    
    def Dominant_Height(self, plotID):
        
        """ Finds the mean height of the two thickest trees in each plot (Mean quadratic diameter of 100 thickest trees/ha of one species [m]). 

        Returns:
            (float): height of the two thickest trees.
        """
        
        data_dict = {'tree_sp':[],'dbh':[], 'height':[]}
        
        document = open(self.treeData)
        line = document.readline()
        while (line):
            split = line.rstrip().split(',')
            if split[0] == plotID:
                data_dict['tree_sp'].append(int(split[2]))
                data_dict['dbh'].append(int(split[3]))
                data_dict['height'].append(int(split[4]))
            
            line = document.readline()
        document.close()
        
        trees = [(data_dict['height'][t]/10,data_dict['dbh'][t], data_dict['tree_sp'][t]) for t in range(len(data_dict['tree_sp']))]
        # dom is the thickest tree in the plot among all the target species
        dom = [x[2] for x in nlargest(1,trees,key=itemgetter(1))]
        # height_largest_dbh is the two tickest trees in the plot
        height_largest_dbh = [x[0] for x in nlargest(2,trees,key=itemgetter(1)) if [x[2]] == dom]

        Ddom = np.mean(height_largest_dbh)
        
        return Ddom, dom



                                                # %%%%%%    converts NFI plots' UTM Coordinates to Latitude/Longitude
       
    def utmToLatLong(self,utmNorthing, utmEasting, utmZone):
        
        """
        This method converts NFI plots' UTM Coordinates to Latitude/Longitude (WGS84).  Based on "node-coordinator" by Larry Moore.
        Adapted from Node-coordinator Project (https://github.com/beatgammit/node-coordinator)
        
        """
        eastingOffset = 500000.0
        northingOffset = 10000000.0
        k0 = 0.9996
        equatorialRadius = 6378137.0
        eccSquared = 0.006694380023
        eccPrimeSquared = eccSquared / (1 - eccSquared)
        e1 = (1 - math.sqrt(1 - eccSquared)) / (1 + math.sqrt(1 - eccSquared));
        rad2deg = 180.0/math.pi

        # Casts input from string to floats or ints
        # Removes 500,000 metre offset for longitude
        xUTM = float(utmEasting) - eastingOffset
        yUTM = float(utmNorthing)
        zoneNumber = int(utmZone)

        # This line below is for debug purposes only, remove for batch processes.
        #print 'The input is: ' + str(utmEasting) + 'm E, ' + str(utmNorthing) + 'm N in NAD83 UTM Zone ' + str(utmZone) + '\n'

        # Finds the origin longitude for the zone
        lonOrigin = (zoneNumber - 1) * 6 - 180 + 3 # +3 puts in zone centre

        M = yUTM / k0 #This finds the meridional arc
        mu = M / (equatorialRadius * (1- eccSquared / 4 - 3 * eccSquared * eccSquared / 64 -5 * eccSquared * eccSquared * eccSquared /256))

        # Calculates the footprint latitude
        phi1Rad = mu + (3 * e1 / 2 - 27 * e1 * e1 * e1 /32) * math.sin(2*mu) + ( 21 * e1 * e1 / 16 - 55 * e1 * e1 * e1 * e1 / 32) * math.sin( 4 * mu) + (151 * e1 * e1 * e1 / 96) * math.sin(6 * mu)
        phi1 = phi1Rad * rad2deg

        # Variables for conversion equations
        N1 = equatorialRadius / math.sqrt( 1 - eccSquared * math.sin(phi1Rad) *  math.sin(phi1Rad))
        T1 = math.tan(phi1Rad) * math.tan(phi1Rad)
        C1 = eccPrimeSquared * math.cos(phi1Rad) * math.cos(phi1Rad)
        R1 = equatorialRadius * (1 - eccSquared) / math.pow(1 - eccSquared * math.sin(phi1Rad) * math.sin(phi1Rad), 1.5)
        D = xUTM / (N1 * k0)

        # Calculate latitude, in decimal degrees
        lat = phi1Rad - ( N1 * math.tan(phi1Rad) / R1) * (D * D / 2 - (5 + 3 * T1 + 10 * C1 - 4 * C1 * C1 - 9 * eccPrimeSquared) * D * D * D * D / 24 + (61 + 90 * T1 + 298 * C1 + 45 * T1 * T1 - 252 * eccPrimeSquared - 3 * C1 * C1) * D * D * D * D * D * D / 720)
        lat = lat * rad2deg
    
        # Calculate longitude, in decimal degrees
        lon = (D - (1 + 2 * T1 + C1) * D * D * D / 6 + (5 - 2 * C1 + 28 * T1 - 3 * C1 * C1 + 8 * eccPrimeSquared + 24 * T1 * T1) * D * D * D * D * D / 120) / math.cos(phi1Rad)
        lon = lonOrigin + lon * rad2deg

        # Print function below is for debug purposes
        #NOTE: THIS IS THE LOCATION WHERE THE NUMBERS ARE ROUNDED TO 5 DECIMAL PLACES
        #print "Lat: " + str(round(lat, 5)) + ", Long: " + str(round(lon,5))
    
        return lat,lon
    
    
                                                # %%%%%    Calculate age of the dominant height tree
        
    def tree_age(self, plotID, species, SI_m):
        """ Calculate the age of the dominant height tree in each plot and replace it with the initial age set to zero
            (age of the dominant trees to calculate the siteindex)
        """
        ageint = [x for x in range(1,1000,1)]

        htd1 = self.Dominant_Height(plotID)[0] - 1.3
#        self.GROWTH.append(htd1) 
        tref= 40
        t1=0
        sp= species

        if sp == "spruce": 
            b1,b2,b3= 18.9206,5175.18,1.1576            
            for a in range (1, len(ageint)):                
                X0 = 0.5 * (SI_m - 1.3 - b1 + sqrt((SI_m - 1.3 - b1) ** 2 + 4 * b2 * (SI_m - 1.3) * tref ** -b3))
                h1 = (b1 + X0) / (1 + (b2 / X0 * ageint[a] ** (-b3))) 
                if (h1 - 1.3)  > htd1:
                    t1 = ageint[a]
                    break
           
        elif sp == "scots_pine": 
            b1,b2,b3= 12.8361,3263.99,1.1758
            for a in range (1, len(ageint)):                
                X0 = 0.5 * (SI_m - 1.3 - b1 + sqrt((SI_m - 1.3 - b1) ** 2 + 4 * b2 * (SI_m - 1.3) * tref ** -b3))
                h1 = (b1 + X0) / (1 + (b2 / X0 * ageint[a] ** (-b3)))
                if (h1 - 1.3)  > htd1:
                    t1 = ageint[a]                    
                    break                
# Birch and broadleaves                
#        elif  sp in birch_species or sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        else:
            b1,b2,K= 394,1.387,7
            for a in range (1, len(ageint)): 
                X0 = sqrt((SI_m - 1.3 -(b1/(K**b2))) ** 2 + 4 * b1 * (SI_m - 1.3) / (tref ** b2))
                h1 = (SI_m - 1.3 +(b1/(K**b2))+ X0) / (2 + 4 * b1 *  ageint[a]  ** (- b2)/(SI_m - 1.3 -(b1/(K**b2))+ X0))
                if (h1-1.3)  > htd1:
                    t1 = ageint[a]
                    break

        if t1 <= 11:
            t1 = 11
        elif t1 > 400:
            t1 = 400
        else:                   
            t1 = ageint[a]   
            
            
        return t1

                                                # %%%%%%    Calculate tree basal area    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    
    def ba(self, dbh):
        """        
        Calculate basal area for each tree, to test in main: print(GrowthModel.ba('138243'))
        Return: tree basal area (m2)
        """

        return pi*(dbh/2000)**2

    
                                                # %%%%%   Calculates biomass, carbon, and equivalent CO2 for a tree  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
    
    def tree_biomass(self,D,H,SP):
        """
        Biomass calculator.
        Calculates biomass, carbon, and equivalent CO2 for a tree given the species, dbh, and height.
        In these calculation, we assume 50% carbon content of the biomass
        
        References
        ---------
        reference1 Marklund, L.G., 1988. Biomass functions for pine, spruce and birch in Sweden (Report No. 45). Swedish University of Agricultural Sciences, UmeÃ¥.
        reference2 Petersson, H. & StAYhl, G. 2006. Functions for below-ground biomass of Pinus sylvestris, Picea abies, Betula pendula and Betula pubescens in Sweden. Scandinavian Journal of Forest Research 21(Suppl 7): 84-93

        Parameters
        ----------
        dbh : Diameter in breast height in centimeter(cm)including bark
        height: Tree height in meter(m)
        sp: tree species (Norway spruce, Scots Pine, Birch, and other broadleaves)
        
        Returns
        -------
        A data with the dry weight biomass (kg) / Carbon/ CO2 for the specified components.
        
        Components
        ----------
        STV: biomass of stem wood            # spruce or pine or birch
        STB: biomass of stem bark            # bark
        --->ST: stem biomass = STV + STB
        LGR: Crown biomass                   #Lbranch
        BAR: foliage biomass                 #needle
        ---> branch biomass = LGR + BAR
        DGR: biomass of dead branches        #DBranch
        STU: stump biomass                   #Stump
        RGE5: biomass of coarse roots        #LgRoot
        RLT5: biomass of fine roots          #SmRoot
        ---> bimass of roots = RGE5 + RLT5
        Total_AGB: Total aboveground biomass (STV+STB+STU+DGR+LGR)
        Total_BGB: Total belowground biomass(using Petersson equations)
        Total tree biomass (Total_AGB + Total_BGB)
        
        Carbon: carbon stored by tree in kg (equivalent mass of carbon)
        CO2: CO2 equivalent of tree biomass

        """

        Carbon_conversion_factor=0.5
        CO2_Fraction = 3.67
        dbh = D / 10 # centimeter
        height = H / 10 # meter
        sp= SP
        
        Compute_biomass_abh = lambda dAdd, dCoef, hCoef, lnhCoef, const: exp(const + dCoef * (dbh/(dbh + dAdd))+ hCoef * height + lnhCoef * log(height))	
        Compute_biomass_ab = lambda dAdd, dCoef, const: exp(const + dCoef * (dbh/(dbh + dAdd)))
        
        
        if sp == "spruce":
            
            
            Biomass_STV = Compute_biomass_abh(14,7.2309,0.0355,0.7030,-2.3032)
            Carbon_STV  = Carbon_conversion_factor * Biomass_STV
            CO2_STV     = CO2_Fraction * Carbon_STV
            
            Biomass_STB = Compute_biomass_abh(15,8.3089,0.0147,0.2295,-3.4020)
            Carbon_STB  = Carbon_conversion_factor * Biomass_STB
            CO2_STB     = CO2_Fraction * Carbon_STB
            
            Biomass_ST = Compute_biomass_abh(14,7.4690,0.0289,0.6828,-2.1702)
            Carbon_ST  = Carbon_conversion_factor * Biomass_ST
            CO2_ST     = CO2_Fraction * Carbon_ST
            
            Biomass_LGR = Compute_biomass_abh(13,10.9708,-0.0124,-0.4923,-1.2063)
            Carbon_LGR  = Carbon_conversion_factor * Biomass_LGR
            CO2_LGR     = CO2_Fraction * Carbon_LGR
            
            Biomass_BAR = Compute_biomass_abh(12,9.7809,0,-0.4873,-1.8551)
            Carbon_BAR  = Carbon_conversion_factor * Biomass_BAR
            CO2_BAR     = CO2_Fraction * Carbon_BAR
            
            Biomass_DGR = Compute_biomass_abh(18,3.6518,0.0493,1.0129,-4.6351) 
            Carbon_DGR  = Carbon_conversion_factor * Biomass_DGR
            CO2_DGR    = CO2_Fraction * Carbon_DGR
            
            Biomass_STU = Compute_biomass_ab(17,10.6686,-3.3645)
            Carbon_STU  = Carbon_conversion_factor * Biomass_STU
            CO2_STU     = CO2_Fraction * Carbon_STU
            
            Biomass_RGE5= Compute_biomass_ab(8,13.3703,-6.3851)
            Carbon_RGE5  = Carbon_conversion_factor * Biomass_RGE5
            CO2_RGE5     = CO2_Fraction * Carbon_RGE5
            
            Biomass_RLT5= Compute_biomass_ab(12,7.6283,-2.5706)
            Carbon_RLT5 = Carbon_conversion_factor * Biomass_RLT5
            CO2_RLT5     = CO2_Fraction * Carbon_RLT5

            bg = (exp((0.32308**2) / 2 + 4.58761 + (dbh*10) / ((dbh*10) + 138) * 10.44035))/1000 # blow ground biomass / Petterson and Stahl 2006 
            Biomass_BGB = bg - Biomass_STU
            Carbon_BGB  = Carbon_conversion_factor * Biomass_BGB
            CO2_BGB     = CO2_Fraction * Carbon_BGB
                        
        elif sp == "scots_pine":

            
            Biomass_STV = Compute_biomass_abh(14,7.6066,0.0200,0.8658,-2.6864)
            Carbon_STV  = Carbon_conversion_factor * Biomass_STV
            CO2_STV     = CO2_Fraction * Carbon_STV
            
            Biomass_STB = Compute_biomass_abh(16,7.2482,0,0.4487,-3.2765)
            Carbon_STB  = Carbon_conversion_factor * Biomass_STB
            CO2_STB    = CO2_Fraction * Carbon_STB
            
            Biomass_ST = Compute_biomass_abh(13,7.5939,0.0151,0.8799,-2.6768)
            Carbon_ST  = Carbon_conversion_factor * Biomass_ST
            CO2_ST     = CO2_Fraction * Carbon_ST
            
            Biomass_LGR = Compute_biomass_abh(10,13.3955,0,-1.1955,-2.5413)
            Carbon_LGR = Carbon_conversion_factor * Biomass_LGR
            CO2_LGR     = CO2_Fraction * Carbon_LGR
            
            Biomass_BAR = Compute_biomass_abh(7,12.1095,0.0413,-1.5650,-3.4781)
            Carbon_BAR  = Carbon_conversion_factor * Biomass_BAR
            CO2_BAR     = CO2_Fraction * Carbon_BAR
            
            Biomass_DGR = Compute_biomass_abh(10,7.1270,-0.0465,1.1060,-5.8926)  
            Carbon_DGR  = Carbon_conversion_factor * Biomass_DGR
            CO2_DGR     = CO2_Fraction * Carbon_DGR
            
            Biomass_STU = Compute_biomass_ab(15,11.0481,-3.9657)
            Carbon_STU  = Carbon_conversion_factor * Biomass_STU
            CO2_STU     = CO2_Fraction * Carbon_STU
            
            Biomass_RGE5= Compute_biomass_ab(10,8.8795,-3.8375)
            Carbon_RGE5  = Carbon_conversion_factor * Biomass_RGE5
            CO2_RGE5     = CO2_Fraction * Carbon_RGE5
            
            Biomass_RLT5= Compute_biomass_ab(9,13.2902,-6.3413)
            Carbon_RLT5  = Carbon_conversion_factor * Biomass_RLT5
            CO2_RLT5    = CO2_Fraction * Carbon_RLT5
            
            Biomass_BGB = (exp((0.35449**2)  / 2 + 3.44275 + (dbh*10) / ((dbh*10) + 113) * 11.06537))/1000     # blow ground biomass
            Carbon_BGB  = Carbon_conversion_factor * Biomass_BGB
            CO2_BGB     = CO2_Fraction * Carbon_BGB

                
        elif sp == "birch":
            
            
            Biomass_STV = Compute_biomass_abh(11,8.1184,0,0.9783,-3.3045)
            Carbon_STV  = Carbon_conversion_factor * Biomass_STV
            CO2_STV     = CO2_Fraction * Carbon_STV
            
            Biomass_STB = Compute_biomass_abh(14,8.3019,0,0.7433,-4.0778)
            Carbon_STB  = Carbon_conversion_factor * Biomass_STB
            CO2_STB     = CO2_Fraction * Carbon_STB
            
            Biomass_ST = Compute_biomass_abh(7,8.2827,0.0393,0.5772,-3.5686)
            Carbon_ST  = Carbon_conversion_factor * Biomass_ST
            CO2_ST    = CO2_Fraction * Carbon_ST
            
            Biomass_LGR = Compute_biomass_ab(10,10.2806,-3.3633)
            Carbon_LGR  = Carbon_conversion_factor * Biomass_LGR
            CO2_LGR     = CO2_Fraction * Carbon_LGR
            
            Biomass_BAR = Biomass_STV  * 0.011/0.52
            Carbon_BAR  = Carbon_conversion_factor * Biomass_BAR
            CO2_BAR     = CO2_Fraction * Carbon_BAR
            
            Biomass_DGR = Compute_biomass_abh(30,11.2872,-0.3081,2.6821,-6.6237) 
            Carbon_DGR  = Carbon_conversion_factor * Biomass_DGR
            CO2_DGR    = CO2_Fraction * Carbon_DGR
            
            Biomass_STU = Compute_biomass_ab(15,11.0481,-3.9657)   # same as pine
            Carbon_STU  = Carbon_conversion_factor * Biomass_STU
            CO2_STU     = CO2_Fraction * Carbon_STU
            
            Biomass_RGE5= Biomass_STV * 0.042/0.52
            Carbon_RGE5 = Carbon_conversion_factor * Biomass_RGE5
            CO2_RGE5     = CO2_Fraction * Carbon_RGE5
            
            Biomass_RLT5= Biomass_STV * 0.042/0.52
            Carbon_RLT5  = Carbon_conversion_factor * Biomass_RLT5
            CO2_RLT5     = CO2_Fraction * Carbon_RLT5
            
            Biomass_BGB = (exp((0.36266**2)  / 2 + 6.1708  + (dbh*10) / ((dbh*10) + 225) * 10.01111))/1000    # blow ground biomass
            Carbon_BGB  = Carbon_conversion_factor * Biomass_BGB
            CO2_BGB     = CO2_Fraction * Carbon_BGB

#        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        
        else:

            
            Biomass_STV = Compute_biomass_abh(11,8.1184,0,0.9783,-3.3045)     
            Carbon_STV  = Carbon_conversion_factor * Biomass_STV
            CO2_STV     = CO2_Fraction * Carbon_STV
            
            Biomass_STB = Compute_biomass_abh(14,8.3019,0,0.7433,-4.0778)
            Carbon_STB  = Carbon_conversion_factor * Biomass_STB
            CO2_STB     = CO2_Fraction * Carbon_STB
            
            Biomass_ST = Compute_biomass_abh(7,8.2827,0.0393,0.5772,-3.5686)
            Carbon_ST  = Carbon_conversion_factor * Biomass_ST
            CO2_ST    = CO2_Fraction * Carbon_ST
            
            Biomass_LGR = Compute_biomass_ab(10,10.2806,-3.3633)
            Carbon_LGR  = Carbon_conversion_factor * Biomass_LGR
            CO2_LGR     = CO2_Fraction * Carbon_LGR
            
            Biomass_BAR = Biomass_STV  * 0.011/0.52
            Carbon_BAR  = Carbon_conversion_factor * Biomass_BAR
            CO2_BAR     = CO2_Fraction * Carbon_BAR
            
            Biomass_DGR = Compute_biomass_abh(30,11.2872,-0.3081,2.6821,-6.6237) 
            Carbon_DGR  = Carbon_conversion_factor * Biomass_DGR
            CO2_DGR    = CO2_Fraction * Carbon_DGR
            
            Biomass_STU = Compute_biomass_ab(15,11.0481,-3.9657) # same as pine
            Carbon_STU  = Carbon_conversion_factor * Biomass_STU
            CO2_STU     = CO2_Fraction * Carbon_STU
            
            Biomass_RGE5= Biomass_STV * 0.042/0.52
            Carbon_RGE5 = Carbon_conversion_factor * Biomass_RGE5
            CO2_RGE5     = CO2_Fraction * Carbon_RGE5
            
            Biomass_RLT5= Biomass_STV * 0.042/0.52
            Carbon_RLT5  = Carbon_conversion_factor * Biomass_RLT5
            CO2_RLT5     = CO2_Fraction * Carbon_RLT5
            
            Biomass_BGB = (exp((0.36266**2)  / 2 + 6.1708  + (dbh*10) / ((dbh*10) + 225) * 10.01111))/1000   # blow ground biomass
            Carbon_BGB  = Carbon_conversion_factor * Biomass_BGB
            CO2_BGB     = CO2_Fraction * Carbon_BGB
            
        Tot_biomass = Biomass_ST  + Biomass_LGR + Biomass_DGR + Biomass_STU + Biomass_BGB 
        Total_carbon = Tot_biomass * Carbon_conversion_factor
        Tot_co2 = Total_carbon * CO2_Fraction
        
        Tot_carbon_stems = Biomass_ST * Carbon_conversion_factor
        Tot_carbon_roots = (Biomass_LGR + Biomass_DGR + Biomass_STU + Biomass_BAR + Biomass_RGE5 + Biomass_RLT5)*Carbon_conversion_factor
        Tot_co2_stems = Tot_carbon_stems * CO2_Fraction
        Tot_co2_roots = Tot_carbon_roots * CO2_Fraction
        
        Tot_biomass_dead   = Biomass_ST
        Total_carbon_dead  = Tot_biomass_dead * Carbon_conversion_factor
        Tot_co2_dead       = Total_carbon_dead * CO2_Fraction
           
        
        return Biomass_BGB, Tot_co2, Tot_biomass, Total_carbon, Biomass_BAR, Biomass_LGR, Biomass_RGE5, Biomass_RLT5, Tot_carbon_stems, Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots, Tot_biomass_dead, Total_carbon_dead, Tot_co2_dead

                                                # %%%%%%    calculate the litter input to Yasso Model  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
    
    def fLitter_Production(self, species, Biomass_BAR,Biomass_LGR,Biomass_RGE5,Biomass_RLT5, LAT):
        """
        This function will calculate the litter input to Yasso Model by using turnover rates for initial conditions
        =================================================================================================
        unwl, ufwl, ucwl: float. kg/m2 (mass/area) of non-woody, fine and coarse woody litter produced in that year.
        unwl(non-woody)           = Foilage + Fine roots(<2 mm)
        ufwl(fine woody litter)   = Branches + Coarse roots(2-5 mm)
        ucwl(coarse woody litter) = Stem
        ========================================================================================================
            Parameter                Species                     Turnover rates(yr-1)                   source
        --------------------------------------------------------------------------------------------------------
        Foilage(Needles)             Pine                     1.656 - (0.0231) * Latitude             Ågren et al.(2007)       
        Foilage(Needles)             Spruce                   0.489 - (0.0063) * Latitude             Ågren et al.(2007) 
        Foilage(Needles)             birch                                0.1                         DeWit et al.2006
        ---------------------------------------------------------------------------------------------------------
        Branches                     pine                               0.027                         DeWit et al.2006
        Branches                     spruce                             0.0125                        DeWit et al.2006
        Branches                     birch                              0.025                         Peltoniemi et al.(2004)   
        ---------------------------------------------------------------------------------------------------------
        Roots(2-5 mm)                pine                               0.10                          Eriksson et al.(2007)  
        Roots(2-5 mm)              spruce                               0.10                          Eriksson et al.(2007)
        Roots(2-5 mm)               birch                               0.10                          Eriksson et al.(2007) 
        ---------------------------------------------------------------------------------------------------------
        Fine root(< 2 mm)            pine                               0.6                   Matamala et al. (2003)
        Fine root(< 2 mm)          spruce                               0.6                   Matamala et al. (2003)
        Fine root(< 2 mm)           birch                               0.6                   Matamala et al. (2003)
        ---------------------------------------------------------------------------------------------------------
        """
        Latitude = LAT
        
        if species == "spruce":
            Foilage1    = 0.489 - (0.0063) * Latitude
            Foilage2    = 1 - Foilage1
            Foilage3    = 1 - Foilage2
            Foilage4    = 1 - Foilage3
            Foilage5    = 1 - Foilage4
            
            Branches1   = 0.0125
            Branches2   = 1 - Branches1
            Branches3   = 1 - Branches2
            Branches4   = 1 - Branches3
            Branches5   = 1 - Branches4
            
            Roots1      = 0.10
            Roots2      = 1 - Roots1
            Roots3      = 1 - Roots2
            Roots4      = 1 - Roots3
            Roots5      = 1 - Roots4

            Fine_root1  =  0.6
            Fine_root2  =  1-Fine_root1
            Fine_root3  =  1-Fine_root2
            Fine_root4  =  1-Fine_root3
            Fine_root5  =  1-Fine_root4
            
        elif species == "scots_pine":
            Foilage1    = 1.656 - (0.0231) * Latitude
            Foilage2    = 1 - Foilage1
            Foilage3    = 1 - Foilage2
            Foilage4    = 1 - Foilage3
            Foilage5    = 1 - Foilage4
            
            Branches1   = 0.027
            Branches2   = 1 - Branches1
            Branches3   = 1 - Branches2
            Branches4   = 1 - Branches3
            Branches5   = 1 - Branches4
            
            Roots1      = 0.10
            Roots1      = 0.10
            Roots2      = 1 - Roots1
            Roots3      = 1 - Roots2
            Roots4      = 1 - Roots3
            Roots5      = 1 - Roots4
            
            Fine_root1  = 0.6
            Fine_root2  =  1-Fine_root1
            Fine_root3  =  1-Fine_root2
            Fine_root4  =  1-Fine_root3
            Fine_root5  =  1-Fine_root4
            
        else:
            Foilage1   =  0.1
            Foilage2    = 1 - Foilage1
            Foilage3    = 1 - Foilage2
            Foilage4    = 1 - Foilage3
            Foilage5    = 1 - Foilage4
            
            Branches1  = 0.025 
            Branches2   = 1 - Branches1
            Branches3   = 1 - Branches2
            Branches4   = 1 - Branches3
            Branches5   = 1 - Branches4
            
            Roots1     = 0.10
            Roots2      = 1 - Roots1
            Roots3      = 1 - Roots2
            Roots4      = 1 - Roots3
            Roots5      = 1 - Roots4
            
            Fine_root1 = 0.6
            Fine_root2  =  1-Fine_root1
            Fine_root3  =  1-Fine_root2
            Fine_root4  =  1-Fine_root3
            Fine_root5  =  1-Fine_root4
            
        unwl   = Foilage5 * Biomass_BAR +  Fine_root5 * Biomass_RLT5
        ufwl   = Branches5 * Biomass_LGR + Roots5 * Biomass_RGE5
        ucwl   = 0
        
        return unwl, ufwl, ucwl 

                                                                # %%%%%    Read the weather data %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
    def readweatherData(self):
        
        with open(self.weatherData) as file:
            next(file)
            reader = csv.reader(file, delimiter=',')
            
            for row in reader:          
                municipalityId        = int(float(row[0]))
                countyId              = int(float(row[1]))
                stationID             = row[2]
                validFrom             = row[3]
                temp                  = float(row[4])

                if temp != 3.3:
                    self.weatherDict[municipalityId]     = temp
                    self.weatherErrorDict[countyId]      = temp
                    self.weatherReferenceTime[stationID] = validFrom 
#                print(data["data"][i]["id"])               

#        print(self.weatherDict[4212])
#        print(self.weatherReferenceTime)
                    
                                                                # %%%%%%   Read the weather data %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        
    def readTree_age_Data(self,plotID, TreeID):

        document = open(self.ageData)
        line = document.readline()
        while (line):
            split = line.rstrip().split(',')
            if (split[0] == plotID) and (int(split[1]) == TreeID):
                age = (int(split[2]))           
            line = document.readline()
        document.close()
        
        return age                   

                                                                # %%%%%   Read the plot level data       
    def readplotData(self):

        """ Read the plot level data as csv file and make an instance.
        format:  plot_id	 Entire_divided_plot      prop_plot	       plot_size	         subplot_size	UTM_Easting   UTM_Northing    
                NFI_Grid_km    Municipality  	altitude_m     soil_depth   	land_type	      land_use	    SI_spp	    SI_m	   veg_type	
                 stand_age_years	   slope_per	    skidding_distance_100m   	ha2plot  	N_tree_ha   	N_tree_plot   	region	
                land_use_class

        Args:
            None.
        Returns:
            None.

        """

        with open(self.plotData) as file:
            next(file)
            reader = csv.reader(file, delimiter=',')
            i=0
            for row in reader:
#                if row[8] ==  "3x3":
                                    
                plot_id =                                   row[0]
                self.plotId_plotlevel.append(plot_id)
                Entire_divided_plot =             int(float(row[1]))                   
                prop_plot =                       int(float(row[2]))
                plot_size=                        int(float(row[3]))
                subplot_size=                     int(float(row[4]))
                self.subplot_sizeDict[plot_id] = subplot_size
                year=                             int(float(row[5]))
                self.years[plot_id] =             year
                UTM_Easting =                     int(float(row[6]))
                UTM_Northing=                     int(float(row[7]))
                NFI_Grid_km=                                row[8]
                Municipality=                     int(float(row[9]))
                altitude_m=                       int(float(row[10]))
                if row[11] != "":
                    soil_depth=                   int(float(row[11]))
                else:
                    soil_depth=                             row[11]
                land_type=                        int(float(row[12]))
                land_use=                         int(float(row[13]))
                SI_spp=                           int(float(row[14]))
                if plot_id not in self.SI_sppDict:
                   self.SI_sppDict[plot_id]= (SI_spp)
                SI_m=                             int(float(row[15]))  # Site index height at age 40 [m]
                if plot_id not in self.SI_mDict:
                   self.SI_mDict[plot_id]= (SI_m)
                veg_type=                         int(float(row[16]))
                stand_age_years=                      float(row[17])
                slope_per=                        int(float(row[18]))
                skidding_distance_100m=           int(float(row[19]))
                ha2plot=                              float(row[20])
                N_tree_ha=                            float(row[21])       # Number of stems per hectare (>=5cm) [n/ha]
                N_tree_plot=                          float(row[22])       ## This can be removed!
                region=                           int(float(row[23]))
                land_use_class=                             row[24]
                zone_num =                                      33
                Latitude = self.utmToLatLong(UTM_Northing, UTM_Easting, zone_num)[0]
                Longitude= self.utmToLatLong(UTM_Northing, UTM_Easting, zone_num)[1]
                if plot_id not in self.LatDict:
                    self.LatDict[plot_id]= (Latitude) 
                    self.LongDict[plot_id] = (Longitude)
                self.GridDict[plot_id]= NFI_Grid_km
                if plot_id not in self.AltDict:
                    self.AltDict[plot_id] = altitude_m
                    
                # MeanAirTemperature = self.MeanAnnualTemp(stationID, year)

                self.plots[plot_id] = plot(plot_id,Entire_divided_plot, prop_plot, plot_size ,subplot_size,year,UTM_Easting,UTM_Northing,
                          NFI_Grid_km, Municipality ,altitude_m,soil_depth , land_type, land_use, SI_spp,SI_m,veg_type,stand_age_years,
                          slope_per,skidding_distance_100m,ha2plot,N_tree_ha,N_tree_plot,region,land_use_class,Latitude,Longitude)
                i+=1



                                                        # %%%%%   Read the tree level data
                
    def readtreeData(self):
        
        """ Read the tree level data as csv file and make an instance.
        format:  plot_id  	tree_id	     tree_sp      dbh	     height    diameter_class   tree_Factor    SI_spp       SI_m
        spruce_species = (1,2,3)
        scots_pine_species =(10,11,20,21,29)
        birch_species=(30,31)
        other_broadleaves_species=(50,51,54,59)
        ROS_species= (32,52,53,56)
        warm_species = (40,41,42,43,44,48,49,55,57,58,70)
        
        Args:
            None.
        Returns:
            None.

        """
        mapstore=[]
        with open(self.treeData) as file:
            next(file)
            reader = csv.reader(file, delimiter=',')
            i=0
            for row in reader:
#                if row[0] in self.GridDict:
                plot_id                     = row[0]
                tree_id                     = int(float(row[1]))
                
                tree_sp                     = int(float(row[2]))
                if tree_sp < 10:
                    species                 = "spruce"
                elif tree_sp >= 10 and tree_sp < 30:
                    species                 = "scots_pine"
                elif tree_sp == 30 or tree_sp == 31:
                    species                 = "birch"
                elif tree_sp in [50,51,54,59]:
                    species                 = "other_broadleaves"
                elif tree_sp in [32,52,53,56]:
                    species                 = "ROS"
                else:
                    species                 = "warm"
                dbh                         =  float(row[3])          ## mm
                mort                        =  int(float(row[4]))/100
                
                height                      =  float(row[5])          ## dm
                diameter_class              =  int(float(row[6]))
                tree_Factor                 =  float(row[7])
                if tree_Factor == 0.0:
                    tree_Factor             =   10000/(self.subplot_sizeDict[plot_id] * 1)
                survival                    =  (1 - mort)
                n_tree                      =  tree_Factor * survival
                ## this makes sure the mortality rate cannot be less than zero
                num_DeadTrees               = tree_Factor * max(mort, 0)
                
                temporary                   =  n_tree
                ba                          = self.ba(dbh)
                if survival == 1:        
                    n_tree = n_tree
                    num_DeadTrees = 0
            
                elif survival <= 0:
                    n_tree = 0
                    num_DeadTrees = temporary
                    ba = 0
            

                """
                When the number of trees goes below 
                """
                Is_tree_dead = n_tree/tree_Factor
                X = 1/(2*tree_Factor)
            
                if tree_Factor != 1:
                    if Is_tree_dead < X:
                        n_tree = 0    
                        num_DeadTrees = temporary
#                volume                      =  float(row[7])
                try:
                    if row[11] != "Nan":
                        SI_spp                  =  int(float(row[11]))
                    else:
                        SI_spp                  =  self.SI_sppDict[plot_id]
                except ValueError as e:
                    print("error",e,"on line",i)
                
                if row[12] != "Nan":
                    SI_m                    =  int(float(row[12]))
                else:
                    SI_m                    =  self.SI_mDict[plot_id]
                
                t_age                       =  int(float(row[13]))
                
                volsum                      =  float(row[14]) * survival
                vol_spruce                  =  float(row[15]) * survival
                vol_pine                    =  float(row[16]) * survival
                vol_birch                   =  float(row[17]) * survival
                vol_others                  =  float(row[18]) * survival
                vol_ROS                     =  float(row[19]) * survival
                vol_warm                    =  float(row[20]) * survival
                dead_volume                 =  volsum * mort
                
                year                        = self.years[plot_id]
                Biomass_tuple               = self.tree_biomass(dbh,height,species)
                BGB                         =  Biomass_tuple[0] * survival
                
                Tot_co2                     =  Biomass_tuple[1] * survival
                Tot_biomass                 =  Biomass_tuple[2] * survival
                Total_carbon                =  Biomass_tuple[3] * survival
                
                Biomass_BAR                 =  Biomass_tuple[4] * survival
                Biomass_LGR                 =  Biomass_tuple[5] * survival
                Biomass_RGE5                =  Biomass_tuple[6] * survival
                Biomass_RLT5                =  Biomass_tuple[7] * survival         
                
                Tot_carbon_stems            =  Biomass_tuple[8] * survival
                Tot_carbon_roots            =  Biomass_tuple[9] * survival
                Tot_co2_stems               =  Biomass_tuple[10] * survival
                Tot_co2_roots               =  Biomass_tuple[11] * survival                
                
                dead_biomass                =  Biomass_tuple[11] * mort
                dead_C                      =  Biomass_tuple[11] * mort
                dead_co2                    =  Biomass_tuple[11] * mort
                
                LAT                         =  self.LatDict[plot_id]
                LONG                        =  self.LongDict[plot_id]
                altitude_m                  =  self.AltDict[plot_id]
                litter_tuple                =  self.fLitter_Production(species,Biomass_BAR,Biomass_LGR,Biomass_RGE5,Biomass_RLT5, LAT)
                unwl                        =  litter_tuple[0]                    
                ufwl                        =  litter_tuple[1]       
                ucwl                        =  litter_tuple[2]
#                t_age                       =   self.readTree_age_Data(plot_id, tree_id)                          
#                print((t_age ))
#                self.heights[tree_id] = height
                self.id_list.append(tree_id) 
                
                try:
                    temp     = self.weatherDict[self.plots[plot_id].Municipality]
#                    referencetime = self.weatherReferenceTime[stationID]
                except KeyError:                
                    temp = self.weatherErrorDict[self.plots[plot_id].region]
#                    referencetime = self.weatherReferenceTime[stationID]
                
                
                coord = np.random.random(2)
                # X and Y of tree coordinates: This is a random number and it will be used for visulaization purpose
                coord = coord[0] * self.gridsize_x , coord[1] * self.gridsize_y
                coord_x = coord[0]
                coord_y = coord[1]
                management = "none"
                
                self.trees[tree_id] = tree(plot_id,tree_id,tree_sp, dbh ,height,diameter_class,tree_Factor, n_tree, volsum, vol_spruce,vol_pine, 
                                           vol_birch, vol_others, vol_ROS, vol_warm, ba, SI_spp,SI_m, BGB,Tot_co2 ,Tot_biomass,Total_carbon, Tot_carbon_stems, 
                                           Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots, Biomass_BAR, Biomass_LGR,Biomass_RGE5, Biomass_RLT5, unwl, ufwl, 
                                           ucwl, LAT,LONG, altitude_m, species, t_age, year ,num_DeadTrees, temp, coord_x, coord_y, dead_volume, dead_biomass, dead_C, dead_co2, management)
                i+=1

#**************************************************************************** To Create TreeDict 

                if plot_id in self.treeDict:
                    self.treeDict[plot_id].append(tree_id)
                else:
                    self.treeDict[plot_id]= [tree_id]
#            print(self.treeDict["B10041"])
#            print(self.plots['B121111'].Municipality)

                # u= self.trees[tree_id].plot_id, self.trees[tree_id].tree_id,  self.trees[tree_id].t_age
                # u=list(u[0:2])
                # mapstore.append(u)
        
        # fexp=open("Individual_tree_ simulator_age.txt",'w')
        # fexp.write ("plot_id tree_id t_age\n")
        # for t in mapstore:
        #     line=' '.join(str(x) for x in t)
        #     fexp.write(line+'\n')
        # fexp.close()
#**************************************************************************** To Create TreeFactorDictionary for the plots in the tree level data
#                
#                if plot_id not in self.treeFactor_Dict.keys():
#                    self.treeFactor_Dict[plot_id]= tree_Factor
#            print(len(self.treeFactor_Dict))


                    
#****************************************************************************                     
#            print(self.trees[299534])                
                
    def VariableBuilder(self):
        
        """ build variables with a value in the another form (dimension).For example: variable soild depth has values 11, 10, 1, 2, 3, 4. 
        We place the levels for these values in another variable: 10 = (> 90% of the area is solid rock); 11 = (lots of open solid rock); 
        1 = (< 25 cm soil depth); 2 = (25-50 cm soil depth); 3 = (50-100 cm soil depth); 4 = (> 100 cm soil depth).
        Moreover, if the plot has no tree, this module generates some trees for development of the growth functions.
            

        Args:
            None.

        Returns:
            None.

        """

        siteIndexNum,siteIndexName,arealuseNum,arealuseNam,arealNum,arealNam,komNUM,komNAM,fylkesNUM,fylkesNAM=[],[],[],[],[],[],[],[],[],[]
        JORDDYBDENum, JORDDYBDEName =[],[]
        mydict, mydict1, mydict2, mydict3, mydict4, mydict5={},{},{},{},{},{}
        with open(self.factors , encoding="utf8", errors='ignore') as file:
            reader = csv.reader(file, delimiter=',')
            for row in reader:
                # land type: 1 productive forest, 12 unproductive forest, 13 other woodland, 2 coastal health land, 
                #22 snowy fields, 30 water, 40 cultural pasture, 41 cultivation, 50 other
                if row[0]!="":
                    landType_num=int(row[0])
                    arealNum.append(landType_num)
                    landType_nam=row[1]
                    arealNam.append(landType_nam)
                    
                # Land use: 1 Forestry, 2 Urban/residential area, 3 cabin field, 4 Military area, 5 Nature reserve, 
                #6 Road/rail/airport, 7 power line, 8 other, 9 recreation area
                    
                if row[2]!="":
                    landUse_num=int(row[2])
                    arealuseNum.append(landUse_num)
                    landUse_nam=row[3]               
                    arealuseNam.append(landUse_nam)
                    
                # Site Index for species: 1 = spruse; 2= pine; 3= birch
                    
                if row[4]!="":
                    sitIndex_num=int(row[4])
                    siteIndexNum.append(sitIndex_num)
                    siteIndex_nam=row[5]               
                    siteIndexName.append(siteIndex_nam)
                    
                    
                if row[6]!="":
                    municipality_num=int(row[6])
                    komNUM.append(municipality_num)
                    municipality_name=row[7]               
                    komNAM.append(municipality_name)
                    
                
                # variable for region. -----> county nr = 10    
                if row[8]!="":
                    fylkes_num=int(row[8])
                    fylkesNUM.append(fylkes_num)
                    fylkes_name=row[9]               
                    fylkesNAM.append(fylkes_name)
                # variable for soil_depth
                
                if row[10]!="":
                    SoilNum=int(row[10])
                    JORDDYBDENum.append(SoilNum)
                    SoilName=row[11]               
                    JORDDYBDEName.append(SoilName)
                    
                    
#**************************************************************************** 

#            H=np.unique(komNAM)
            for h in komNUM:
                mydict[h] = komNAM[komNUM==h]
                komNAM.pop(0)
#            KOM=mydict.values()
#            KODE=mydict.keys()
#            print(mydict)            

            for h in fylkesNUM:
                mydict1[h] = fylkesNAM[fylkesNUM==h]
                fylkesNAM.pop(0)
#            FYLKESNAM=mydict1.values()
#            FYLKESNUM=mydict1.keys()
 #           print(mydict1)

            for h in arealNum:
                mydict2[h] = arealNam[arealNum==h]
                arealNam.pop(0)
#            print(mydict2)


            for h in arealuseNum:
                mydict3[h] = arealuseNam[arealuseNum==h]
                arealuseNam.pop(0)
#            print(mydict3)

                    
            for h in siteIndexNum:
                mydict4[h] = siteIndexName[siteIndexNum==h]
                siteIndexName.pop(0)
#            print(mydict4)
                
            for h in JORDDYBDENum:
                mydict5[h] = JORDDYBDEName[JORDDYBDENum==h]
                JORDDYBDEName.pop(0)
#            print(mydict5)
                
                            
#**************************************************************************** 
        


        mapstore=[]

           
        with open(self.plotData) as file:
            next(file)
            reader = csv.reader(file, delimiter=',')
            for row in reader:                
#                if row[8] ==  "3x3":
                plot_id =                                   row[0]

                self.plots[plot_id].MunicipalityName=mydict[self.plots[plot_id].Municipality]
                self.plots[plot_id].region_name=mydict1[self.plots[plot_id].region]
                self.plots[plot_id].land_type_levels=mydict2[self.plots[plot_id].land_type]
                self.plots[plot_id].land_use_levels=mydict3[self.plots[plot_id].land_use]
                if self.plots[plot_id].SI_spp != 4:
                    self.plots[plot_id].SI_spp_levels=mydict4[self.plots[plot_id].SI_spp]
                else:
                    self.plots[plot_id].SI_spp_levels= "Others"
                if self.plots[plot_id].soil_depth != "":
                    self.plots[plot_id].soil_depth_type=mydict5[self.plots[plot_id].soil_depth]
                else:
                    self.plots[plot_id].soil_depth_type= None

                if plot_id in self.treeFactor_Dict.keys():
                    self.plots[plot_id].treeFactor=self.treeFactor_Dict[plot_id]
                    
                if self.treeDict[plot_id] != []:
                
                    self.plots[plot_id].treeList = self.treeDict[plot_id]
                
                else:
                    
                    plot_id                                = plot_id
                    if self.plots[plot_id].SI_spp == 1:
                        tree_sp                            = 3
                    elif self.plots[plot_id].SI_spp == 2:
                        tree_sp                            = 10
                    else:
                        tree_sp                            = 30

                    tree_id                                =  self.tree_ids(plot_id)
                     
                    if tree_sp == 3:
                        species                            = "spruce"
                    elif tree_sp == 10:
                        species                            = "scots_pine"
                    elif tree_sp == 30:
                        species                            = "birch"

                    SI_m                                   = self.plots[plot_id].SI_m
                    dbh                                    =  50         ## mm
                    mort                                   = 0.
                    dbh_cm                                 = dbh/10
                    if species == "spruce":
                        b1, b2 =  1.877,  0.3276
                        V_u1 , Cov_u1_u2, V_u2, R =  0.286,  -0.00858, 0.000942, 0.1905
                    
                    elif species == "scots_pine":
                        b1, b2 =  1.5007,  0.3747
                        V_u1 , Cov_u1_u2, V_u2 , R = 0.4334, - 0.00729, 0.001891, 0.1784
                    else:
                        b1, b2 =  1.1962, 0.4171
                        V_u1 , Cov_u1_u2, V_u2 , R= 0.2481, - 0.01575, 0.002974, 0.1568
                    
                    a = np.array([[V_u1,Cov_u1_u2], [Cov_u1_u2,V_u2]]) 
                    D = np.linalg.det(a)
                    
                    
                    mu, sigma = 0, D
                    u1 = np.random.normal(mu, sigma, 1)
                    u2 = np.random.normal(mu, sigma, 1)
                    epsilon = (mu, R, 1)

                    height                                   = ((1.3 +((dbh_cm)/(b1+u1[0]+(b2+u2[0])*dbh_cm))**3) + epsilon[0]) * 10    # convert to dm                   
#                    print(height)
                    diameter_class                           =  5
                    tree_Factor                              =  10000/(250 * 1)
                    volume                                   = 0.
                    Inc                                      = 0.
                    Biomass                                  = 0.
                    n_tree                                   =  tree_Factor 
                    SI_spp                                   =  self.plots[plot_id].SI_spp               
                    t_age                                    =  self.tree_age(plot_id, species, SI_m)
                    ba                                       = self.ba(dbh)    # m2
                    volsum                                   =  ba *  height/10 * tree_Factor * 0.4   #(m2*m*1/ha)
                    if species == "spruce":
                        vol_spruce                           =  volsum
                        vol_pine                             = 0.
                        vol_birch                            = 0.
                    elif species == "scots_pine":                    
                        vol_spruce                           = 0.
                        vol_pine                             = volsum
                        vol_birch                            = 0.
                    else:
                        vol_spruce                           = 0.
                        vol_pine                             = 0.
                        vol_birch                            = volsum                        
                        
                    vol_others                               =  0.
                    vol_ROS                                  =  0.
                    vol_warm                                 =  0.
                    
    #                 year                                     = self.years[plot_id]
    #                 Biomass_tuple                            = self.tree_biomass(dbh,height,species)
    #                 BGB                                      =  Biomass_tuple[0]
    #                 Tot_co2                                  =  Biomass_tuple[1]
    #                 Tot_biomass                              =  Biomass_tuple[2]
    #                 Total_carbon                             =  Biomass_tuple[3] 
    #                 Biomass_BAR                              =  Biomass_tuple[4]
    #                 Biomass_LGR                              =  Biomass_tuple[5]
    #                 Biomass_RGE5                             =  Biomass_tuple[6]
    #                 Biomass_RLT5                             =  Biomass_tuple[7]          
    #                 Tot_carbon_stems                         =  Biomass_tuple[8]
    #                 Tot_carbon_roots                         =  Biomass_tuple[9]
    #                 Tot_co2_stems                            =  Biomass_tuple[10]
    #                 Tot_co2_roots                            =  Biomass_tuple[11]
    #                 LAT                                      =  self.LatDict[plot_id]
    #                 LONG                                     =  self.LongDict[plot_id]
    #                 altitude_m                               =  self.AltDict[plot_id]
    #                 litter_tuple                             =  self.fLitter_Production(species,Biomass_BAR,Biomass_LGR,Biomass_RGE5,Biomass_RLT5, LAT)
    #                 unwl                                     =  litter_tuple[0]                    
    #                 ufwl                                     =  litter_tuple[1]       
    #                 ucwl                                     =  litter_tuple[2]
    # #                t_age                       =   self.readTree_age_Data(plot_id, tree_id)                          
    # #                print((t_age ))
    # #                self.heights[tree_id] = height
    #                 self.id_list.append(tree_id) 
                    
    #                 try:
    #                     temp                                 = self.weatherDict[self.plots[plot_id].Municipality]
    # #                    referencetime = self.weatherReferenceTime[stationID]
    #                 except KeyError:                
    #                     temp                                 = self.weatherErrorDict[self.plots[plot_id].region]
    # #                    referencetime = self.weatherReferenceTime[stationID]
                    
                    
    #                 coord                                    = np.random.random(2)
    #                 # X and Y of tree coordinates: This is a random number and it will be used for visulaization purpose
    #                 coord                                    = coord[0] * self.gridsize_x , coord[1] * self.gridsize_y
    #                 coord_x                                  = coord[0]
    #                 coord_y                                  = coord[1]
                    
                    self.TITLES.append(titles_NewTree.ItemTD(plot_id,tree_id,tree_sp,dbh,mort, height,diameter_class,tree_Factor,volume, Inc,Biomass, SI_spp,SI_m, t_age, volsum,
                                 vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm))
                    
                    self.plots[plot_id].treeList = self.treeDict[plot_id]
                    
                    # if plot_id in self.treeDict:
                    #     self.treeDict[plot_id].append(tree_id)
                    # else:
                    #     self.treeDict[plot_id]= [tree_id]

                        
#            print(self.plots["B072291"].treeList)

## This part is used to write a file for projecting the plots                
#                u= self.plots[plot_id].plot_id, self.plots[plot_id].Latitude, self.plots[plot_id].Longitude, self.plots[plot_id].SI_spp_levels, self.plots[plot_id].region_name
#                u=list(u[0:5])
#                mapstore.append(u)
#                
#        fexp=open("plots_projection.txt",'w')
#        fexp.write ("plot_id Latitude Longitude species region\n")
#        for t in mapstore:
#            line=' '.join(str(x) for x in t)
#            fexp.write(line+'\n')
#        fexp.close()
#                          
    def tree_id_generation(self, plot_id):
        
        tree_id = get_random_string(length=len(str(19023398)), allowed_chars='1234567890')

        return tree_id
    
    def tree_ids(self, plot_id):
        
        while True:
            id_= self.tree_id_generation(plot_id)
            if id_ not in self.plots[plot_id].treeList:
                tree_id = id_
                break
        
        return id_
    
                                                # %%%%%
                                
class tree():
    
    """ Provides an object for the tree level data.

    Args:
        plot_id (str): 
        tree_id (int): 
        tree_sp (int): 
        dbh(float):
        height(float):
        diameter_class(int):
        tree_Factor(float):
        SI_spp(int):
        SI_m(int):
        Tot_co2(float):
        Tot_biomass(float):
        Total_carbon(float):
        BGB(float):
        n_tree(float):
        volsum (float):
        vol_spruce (float):
        vol_pine (float):
        vol_birch (float):
        vol_others (float):
        vol_ROS (float):
        vol_warm (float):
        ba (float):
        SI_spp (int): 
        SI_m (int): 
        BGB (float):
        Tot_co2 (float):
        Tot_biomass (float):
        Total_carbon (float):
        Biomass_BAR (float):
        Biomass_LGR (float):
        Biomass_RGE5 (float):
        Biomass_RLT5 (float):
        unwl (float):
        ufwl (float):
        ucwl (float):
        LAT (deg):
        LONG (deg):
        altitude_m (int): 
        species (str):  
        t_age (int): 
        year (int): 
        temp (deg):
        Tot_carbon_stems (float):
        Tot_carbon_roots (float):
        Tot_co2_stem (float):
        Tot_co2_roots (float):
        coord_x (float):
        coord_y (float):

    Attributes:
        plot_id (str):  
        tree_id (int): 
        tree_sp (int): 
        dbh(int):
        height(int):
        diameter_class(int):
        tree_Factor(float):
        SI_spp(int):
        SI_m(int):  
        Tot_co2(float):
        Tot_biomass(float):
        Total_carbon(float):
        BGB(float):
        temp(string):
        n_tree(float):
        volsum (float):
        vol_spruce (float):
        vol_pine (float):
        vol_birch (float):
        vol_others (float):
        vol_ROS (float):
        vol_warm (float):
        ba (float):
        SI_spp (int): 
        SI_m (int): 
        BGB (float):
        Tot_co2 (float):
        Tot_biomass (float):
        Total_carbon (float):
        Biomass_BAR (float):
        Biomass_LGR (float):
        Biomass_RGE5 (float):
        Biomass_RLT5 (float):
        unwl (float):
        ufwl (float):
        ucwl (float):
        LAT (deg):
        LONG (deg):
        altitude_m (int): 
        species (str):  
        t_age (int): 
        year (int): 
        temp (deg):
        Tot_carbon_stems (float):
        Tot_carbon_roots (float):
        Tot_co2_stem (float):
        Tot_co2_roots (float):
        coord_x (float):
        coord_y (float):
    """
	
    def __init__(self,plot_id,tree_id,tree_sp,dbh, height,diameter_class,tree_Factor,n_tree,volsum, vol_spruce,vol_pine, 
                                           vol_birch, vol_others, vol_ROS, vol_warm, ba, SI_spp,SI_m,BGB, Tot_co2, Tot_carbon_stems, 
                                           Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots, Tot_biomass,Total_carbon, Biomass_BAR, 
                                           Biomass_LGR,Biomass_RGE5, Biomass_RLT5,unwl, ufwl, ucwl, LAT,LONG, altitude_m, species, 
                                           t_age,year, num_DeadTrees, temp, coord_x, coord_y, dead_volume, dead_biomass, dead_C, dead_co2, management):
        
        self.plot_id = plot_id
        self.tree_id = tree_id
        self.tree_sp = tree_sp
        self.dbh=dbh
        self.height=height
        self.diameter_class = diameter_class
        self.tree_Factor = tree_Factor
        self.n_tree = n_tree
#        self.volume = volume
        self.volsum = volsum
        self.vol_spruce = vol_spruce
        self.vol_pine = vol_pine
        self.vol_birch = vol_birch
        self.vol_others = vol_others
        self.vol_ROS = vol_ROS
        self.vol_warm = vol_warm
        self.ba = ba
        self.SI_spp = SI_spp
        self.SI_m = SI_m
        self.BGB = BGB
        self.Tot_co2 = Tot_co2
        self.Tot_biomass = Tot_biomass
        self.Total_carbon = Total_carbon
        self.Biomass_BAR = Biomass_BAR
        self.Biomass_LGR = Biomass_LGR
        self.Biomass_RGE5 = Biomass_RGE5
        self.Biomass_RLT5 = Biomass_RLT5
        self.unwl = unwl   
        self.ufwl = ufwl 
        self.ucwl = ucwl 
        self.LAT = LAT
        self.LONG = LONG
        self.altitude_m = altitude_m
        self.species = species
        self.t_age = t_age
        self.year = year
        self.num_DeadTrees = num_DeadTrees
        self.temp = temp
        self.Tot_carbon_stems = Tot_carbon_stems
        self.Tot_carbon_roots = Tot_carbon_roots
        self.Tot_co2_stems = Tot_co2_stems
        self.Tot_co2_roots = Tot_co2_roots
        self.coord_x = coord_x
        self.coord_y = coord_y    
        self.dead_volume = dead_volume
        self.dead_biomass = dead_biomass
        self.dead_C = dead_C
        self.dead_co2 = dead_co2
        self.management = management
#        self.referencetime = referencetime

        
    def __str__(self):
        return 'plot_id\n\t{}\n\ntree_id\n\t{}\n\ntree_sp\n\t{}\n\ndbh\n\t{}\n\nheight\n\t{}\n\ndiameter_class\n\t{}\n\ntree_Factor\n\t{}\n\nSI_spp\n\t{}\n\nSI_m\n\t{}\n\nLAT\n\t{}\n\nLONG\n\t{}\n\nspecies\n\t{}\n\nt_age\n\t{}\n'.format(self.plot_id, 
                           self.tree_id, self.tree_sp, self.dbh, self.height, self.diameter_class,self.tree_Factor, self.SI_spp,self.SI_m, self.LAT, self.LONG, self.species, self.t_age)
    
    

                                                # %%%%%%%
        
class plot():
    
    """ Provides an object for the plot level data.

    Args:
        plot_id (str):
        Entire_divided_plot(int):
        prop_plot (int): 
        plot_size(int):
        subplot_size(int):
        year(int):
        NFI_Grid_km(str):
        Municipality(int):
        altitude_m(int):
        soil_depth(int):
        land_type(int):
        land_use(int):
        SI_spp(int):
        SI_m(int):
        veg_type(int):
        stand_age_years(float):
        slope_per(int):
        skidding_distance_100m(int):
        ha2plot(float):
        N_tree_ha(float):
        N_tree_plot(float):
        region(int):
        land_use_class(str):
        UTM_Easting(int):
        UTM_Northing(int):
        Latitude(float):
        Longitude(float):
        treeList(list):
        tree_Factor(float):

    Attributes:
        
        plot_id (str):
        Entire_divided_plot(int):
        prop_plot (int): 
        plot_size(int):
        subplot_size(int):
        year(int):
        NFI_Grid_km(str):
        Municipality(int):
        altitude_m(int):
        soil_depth(int):
        land_type(int):
        land_use(int):
        SI_spp(int):
        SI_m(int):
        veg_type(int):
        stand_age_years(float):
        slope_per(int):
        skidding_distance_100m(int):
        ha2plot(float):
        N_tree_ha(float):
        N_tree_plot(float):
        region(int):
        land_use_class(str):
        soil_depth_type(str):
        MunicipalityName(str):
        region_name(str):
        land_type_levels(str):
        land_use_levels(str):
        SI_spp_levels(str):
        UTM_Easting(int):
        UTM_Northing(int):
        Latitude(float):
        Longitude(float):
        treeList(list):
        tree_Factor(float):
        
    """
    
    def __init__(self,plot_id,Entire_divided_plot, prop_plot,plot_size, subplot_size, year,UTM_Easting,UTM_Northing,NFI_Grid_km, Municipality, altitude_m, soil_depth, land_type, 
                 land_use, SI_spp,SI_m,veg_type,stand_age_years,slope_per,skidding_distance_100m, ha2plot,N_tree_ha,N_tree_plot,
                 region,land_use_class,Latitude,Longitude):
        
        self.plot_id = plot_id
        self.Entire_divided_plot = Entire_divided_plot
        self.prop_plot = prop_plot
        self.plot_size=plot_size
        self.subplot_size=subplot_size
        self.year=year
        self.UTM_Easting=UTM_Easting
        self.UTM_Northing=UTM_Northing
        self.NFI_Grid_km=NFI_Grid_km
        self.Municipality=Municipality
        self.altitude_m=altitude_m
        self.soil_depth=soil_depth
        self.land_type=land_type
        self.land_use=land_use
        self.SI_spp=SI_spp
        self.SI_m = SI_m
        self.veg_type = veg_type
        self.stand_age_years= stand_age_years
        self.slope_per=slope_per
        self.skidding_distance_100m=skidding_distance_100m
        self.ha2plot=ha2plot
        self.N_tree_ha = N_tree_ha
        self.N_tree_plot = N_tree_plot
        self.region= region
        self.land_use_class=land_use_class
        self.Latitude=Latitude
        self.Longitude=Longitude
        self.soil_depth_type=0
        self.MunicipalityName=0
        self.region_name=0
        self.land_type_levels=0
        self.land_use_levels=0
        self.SI_spp_levels=0
        self.treeList=list()  
        self.treeFactor=0
#        self.MeanAirTemperature = MeanAirTemperature
             
                                                    # %%%%%%% 
""" NOTE:
    Management prescription Class is adapted from Forpylib Project (https://github.com/muldars/forpylib)       
"""

class Management_prescription():
    """ Forest management alternatives (sequence of silvicultural operations) at plot level is a class to be applied to a plot 
        during the projection period. It creates a new plot forest management prescription object for 40 periods of 5 years length
        
        Args:
            
            periods : int,
                  number of projection periods

            interval : int,
                   period length in years
    """
    
    def __init__(self, plot, management, periods=1, interval=1):
        self.interval = int(interval)
        self.periods = int (periods)
        self.p = np.arange(1, self.periods + 1, dtype=np.int)
        self.management = management
        self.mic = management['MIC_no']
        self.plot = plot
        self.actions = pd.DataFrame({'plot_id': self.plot.plot_id, 'p': self.p, 'TI': 0., 'TR': 0.},
                                        index=pd.Index(self.p, name='period'))
        
    def add_clear_cut(self, period):
        """Adds a clear cut harvest to the prescription

        :Parameters:
        
            period : int, 
                     clear cut harvest period in the range [1..self.periods] 
        
        :Returns:
        
            Bool (True or False), 
                  True if the action has been succesfully added to the presciption, False otherwise

        :Examples:
            
            clear cut harvest at period 9 
    
            >>> self.prescription.add_clear_cut(period=9)
            True
        """
        return self.add_thin(period=period, TI=85.0, TR=1.0)

    def add_seedtree_cut(self, period):
        """Adds a seed_tree cut harvest to the prescription

        :Parameters:
        
            period : int, 
                     seed tree cut harvest period in the range [1..self.periods] 
        
        :Returns:
        
            Bool, 
                  True if the action has been succesfully added to the presciption,
                  False otherwise

        :Examples:
        
            seed_tree cut harvest at period 9 
    
            >>> self.prescription.add_seedtree_cut(period=9)
            True
        """
        return self.add_thin(period=period, TI=83.0, TR=1.0)

    def add_thin(self, period, TI=0.0, TR=1.0):
        """based on the management alternatives this method adds a thinning to the prescription writer

        :Parameters:
    
            TI : float,
                 thinning intensity: it is a description of how many trees, how much basal area or how much volume will be removed from the plot. 
                 (In our case, the maximum the percentage of trees to remove is 35%)
    
            TR : float,
                 thinning ratio or plot basal area removal ratio: ratio of the basal area removed to basal area of before thinning.
                 Basal area of removed trees will be clacuated based on the basal area before thinning minus minimum basal area after 
                 thinning which is 22 m^2 in our case
                 in the range [0.0..1.0]

        :Returns:
        
            bool, 
                  True if the action has been succesfully added to the presciption,
                  False otherwise

        :Examples:

            Thinning at period 4 in which 35% of trees are removed
            with a plot basal area removal ratio of 1.0 (sistematic thinning)

            >>> self.prescription.add_thin(period=4, TI = 35, TR=1.0)
            True
        """

        if (0 < period <= self.periods) and (0 < TI <= 100) and (0.0 <= TR <= 1.0):
            self.actions.TI[period] = TI
            self.actions.TR[period] = TR
            return True
        else:
            return False



                                                # %%%%% 
""" NOTE:
    Small part of Simulator class is adapted from Forpylib Project (https://github.com/muldars/forpylib)      
"""
   
class Simulator():
    """
    This class generates plot level tables on the basis of the initial state of the plots and the specified management prescriptions. 
    
    Args:
        prescription : simulation.Management_prescription
                       a instance of class to specify forest management 
                       prescriptions (sequence of operations) at plot leve
        
            
        plot : growth_models,
                the initial state of a plot of a given species for which
                there exists a dynamic plot growth modell
        
        YearN : bool,
                   if True, the prescription is applied from the year: plot.t
                   if False, the prescription is applied from the year: zero
            
    """
    GROWTH1=list()
    treeObj = 0
    def __init__(self, plot,  jobDir, scenario, Harvest_age,  MIC_TYPE, unique,  YearN = False, **kwargs):
        
        self.jobDir = jobDir
        
        self.input = os.path.join(jobDir,'Input')
        self.output = os.path.join(jobDir,'outputs')
        self.output_Mgt = os.path.join(jobDir,'outputMgt')
        self.name = os.path.basename(self.jobDir)
        self.mgt = {"thin":1., "clear cut":2., "seed tree cut":3., "Site_prep":4, "Fertilization":5, "none":0, "not_valid":-1}
        self.plot = plot        
        self.unique = unique        
        self.treeObj= kwargs["Data"]
        self.managementData = "Input/Management_Alternatives.csv"
        # Instantiate a Management_prescription object with our management data file
        self.prescription = Management_prescription(plot, management= pd.read_csv(os.path.join(self.jobDir,self.managementData) , sep=',', index_col=False, dtype='unicode'),
                                                            interval= interval, periods=steps)
        self.scenario = scenario
        self.Harvest_age = Harvest_age
        self.MIC_TYPE = MIC_TYPE
        
        if YearN:
            self.inc = 0
            self.p = np.arange(1, 1 + self.prescription.periods - self.inc , dtype=np.int)
            self.t = (self.p - 1) * self.prescription.interval + self.plot.t  +  self.prescription.interval

            self.year = (self.p - 1) * self.prescription.interval + self.plot.year  +  self.prescription.interval
            self.prescription.actions['t'] = ((self.p - 1) * self.prescription.interval + self.plot.t + self.prescription.interval)
        else:
            self.inc = (np.floor(((self.prescription.interval / 2.0) +  self.plot.t) / self.prescription.interval))
            self.p = np.arange(1, 1 + self.prescription.periods - self.inc , dtype=np.int)
            self.t = (self.inc * self.prescription.interval ) +  ((self.p-1) * self.prescription.interval + self.prescription.interval)
            self.year = (self.p - 1) * self.prescription.interval + self.plot.year  +  self.prescription.interval
            self.prescription.actions['t'] = ((self.prescription.actions.p - 1) * self.prescription.interval  + self.prescription.interval)
        
        self.t2 = self.t + self.prescription.interval
        self.simulation = self.get_simulation() 
           
   
    def current_working_directory(self, directory): 
        if(os.path.exists(directory)):
            os.chdir(directory)
            cwd = os.getcwd()
        return cwd

    def mkdir(self, name):
        if not os.path.exists(name):
            os.mkdir(name)
        assert os.path.isdir(name)  

           
    def get_simulation(self, columns = (['plot_id.MIC_no.p', 'plot_id','MIC_no','p','mgt','t','Year', 'H0','Gr_stock','Gr_stock_spruce','Gr_stock_pine', 'Gr_stock_birch', 'Gr_stock_others', 'Gr_stock_ros','Gr_stock_warm',
                                        'Nb', 'Gb', 'Vb','Vb_spruce' , 'Vb_pine'  ,'Vb_birch' , 'Vb_others' , 'Vb_ros' , 'Vb_warm' , 'Nr', 'Gr', 'Vr_tot','Vr_spruce','Vr_pine','Vr_birch','Vr_others','Vr_ros','Vr_warm', 
                                        'Na','Ga', 'Va' , 'Total_carbon_stock', 'carbon_living','co2_living','carbon_stems' , 'carbon_roots' , 'co2_stems' , 'co2_roots',
                                        'R_carbon','R_carbon_stems','R_co2_stems', 'R_carbon_roots' , 'R_co2_roots','R_co2','Dead_wood_co2' ,'Dead_wood_carbon',
                                        'R_SPulp','R_SSaw','R_PPulp', 'R_PSaw','R_HPulp','R_HSaw','soilC', 
                                        'biodiversity', 'BI1', 'BI2', 'BI3','BI4', 'BI5', 'Richness','Shannon','Deadwood','Lsize_deciduous','Lsize_All'])):
       
        """Generates a dataset with the simulated stand table
        
        Parameters:
   
            colums : array,
                name of plot variables to include in the dataset

        Returns:

            ds : pandas.dataset,
            Dead_wood_co2: Co2 emitted from stems and barks plus the branches left on site
            Dead_wood_carbon: amount of C from stems and barks plus the branches left on site
        """ 
         
  
        ds0 = {'Year':self.plot.year  ,'t': self.plot.t,'tst': self.plot.t-self.prescription.interval,
               't2': self.plot.t + self.prescription.interval,
               'mortality':self.plot.mortality,'Gr_stock': self.plot.V, 'Vra': 0.0, 
               'H0': self.plot.H0, 'Na': self.plot.N, 'Ga': self.plot.G, 
               'interval':self.prescription.interval}

        
        ds = pd.DataFrame({    'plot_id.MIC_no.p':"",
                               'plot_id':0.,              
                               'MIC_no':0,
                               'p': self.p,
                               'new_p':"",
                               'plot_id.MIC_no':"",
                               't': self.t,
#                               't2': self.t2,
                               'Year':self.year,
                               'mortality':True,
                               'mic_type': 0.,
                               'new_mic': "",
                               'mgt': self.mgt["not_valid"],
                               'Gr_stock':0., 'Gr_stock_spruce':0., 'Gr_stock_pine':0., 'Gr_stock_birch':0., 'Gr_stock_others':0., 'Gr_stock_ros':0., 'Gr_stock_warm':0.,
                               'Nb': 0., 'Gb': 0., 'Vb': 0., 'Vb_spruce':0., 'Vb_pine':0., 'Vb_birch':0., 'Vb_others':0., 'Vb_ros':0., 'Vb_warm':0., 'H0': 0.,'Nr': 0., 'Gr': 0., 
                               'Vr_tot': 0., 'Vr_spruce': 0.,'Vr_pine': 0.,'Vr_birch': 0.,'Vr_others': 0.,'Vr_ros': 0.,'Vr_warm': 0.,'Na': 0., 'Ga': 0.,'Va':0., 'Vra': 0.,'PAI': 0., # 'POT':0.,'Dg': 0.,
                               'HBI': 0., 'tst': -1.0, 'Initial_BGB_living': 0.,'Initial_co2_living': 0.,'Initial_biomass_living':0., 'Initial_carbon_living': 0.,'Initial_carbon_stems_living': 0.,
                               'Initial_carbon_roots_living': 0.,'Initial_co2_stems_living': 0.,'Initial_co2_roots_living': 0., 'biomass_living': 0., 'carbon_living': 0., 'R_carbon': 0.,'co2_living': 0.,
                               'R_BGB': 0.,'R_carbon_stems': 0.,'R_co2_stems': 0.,'R_carbon_roots': 0.,'R_co2_roots': 0.,
                               'R_co2': 0., 'biodiversity': 0,'BI1': 0. ,'BI2': 0. ,'BI3': 0. ,'BI4': 0. ,'BI5': 0.,'Richness':0.,'Shannon':0.,'Deadwood':0.,'Lsize_deciduous':0.,'Lsize_All':0. ,
                               'Live_biomass': 0., 'R_biomass': 0., 'Dead_wood_co2': 0., 'Dead_wood_biomass': 0., 'Dead_wood_carbon': 0.,'Total_carbon_stock':0., 
                               'carbon_stems':0.,  'carbon_roots':0.,  'co2_stems':0.,   'co2_roots':0.,'R_SSaw': 0., 'R_PSaw': 0. ,'R_HSaw': 0. ,'R_SPulp': 0.,'R_PPulp': 0.,'R_HPulp':0.,'soilC':0.,                
                               'interval':self.prescription.interval}, index=pd.Index(self.p,name='period'))
        
        Next_Rotation_age = 0.
        Thinn_age = 0
        Number_Thinn = 1
        Establishment_age = 0
        Clear_cut_tag = False
        seed_tree_cut_tag = False
        Thinn_MS_tag = False
        Thinn_MP_tag = False
        Thinn_HS_tag = False
        Thinn_HP_tag = False
        Thinn_LS_tag = False
        fertilization = False
        Site_prep_after_harvesting = False
         
        volume_deadwood_p0 = 0
        # ***************************************************************************************************
        dfGE_15 = self.prescription.management[self.prescription.management['Site index'] == "GE_15.5"]
        dfGE_15_MIC_no = dfGE_15["MIC_no"].unique().tolist()
        df10_15 = self.prescription.management[self.prescription.management['Site index'] == "10.5-15.5"]
        df10_15_MIC_no = df10_15["MIC_no"].unique().tolist()
        dfL_10 = self.prescription.management[self.prescription.management['Site index'] == "L_10.5"]
        dfL_10_MIC_no = dfL_10["MIC_no"].unique().tolist() 
                    
        
        if (__SI__ >= 15.5):
            SCENARIOS = dfGE_15_MIC_no
        elif (__SI__ < 15.5) and (__SI__ >= 10.5):
            SCENARIOS = df10_15_MIC_no
        else:
            SCENARIOS = dfL_10_MIC_no 
            
## ***************************************************************************************************   
## ***************************************************************************************************

        unwanted_indices = [] 

        for i in ds.index:
                       
            ds.mic_type[i] = self.plot.fMic(**ds0)
            
            if ds.mic_type[i] == "High_spruce" and self.MIC_TYPE in ["High_spruce", "Medium_spruce" , "Low_spruce"]:
                ds.mic_type[i] = self.MIC_TYPE
            elif ds.mic_type[i] == "High_pine" and self.MIC_TYPE in ["High_pine", "Medium_pine"]:
                ds.mic_type[i] = self.MIC_TYPE
            elif ds.mic_type[i] ==  "broadleaf" and self.MIC_TYPE in ["broadleaf", "No_man"] :
                ds.mic_type[i] = self.MIC_TYPE
            else:
                ds.mic_type[i] = "NONE"
            
            
            ds.H0[i] = float(format((self.plot.fH0(Increment = False, **ds0)), '.2f'))
            ds.plot_id[i] = self.plot.plot_id
#            ds.POT[i] = float(format((self.plot.fPOT(**ds0)), '.2f'))
            ds.Gb[i] = float(format((self.plot.fGp(i, **ds0)), '.2f'))
            ds.tst[i] =  ds0['tst'] + self.prescription.interval
            
            ds.mortality[i] =  self.plot.mortality        
            
            self.plot.UpdateTrees(ds.mortality[i], ds.Year[i], ds.p[i]) 

            ds.Nb[i] = float(format((self.plot.fN(**ds0)), '.2f'))
            ds.HBI[i] = float(format((100 * np.sqrt(10000 / ds.Nb[i]) / ds.H0[i]), '.2f'))
            VOLUME = self.plot.fV(i, **ds.loc[i])
            ds.Vb[i]        = float(format(VOLUME[0], '.2f'))  
            ds.Vb_spruce[i] = float(format(VOLUME[1], '.2f'))   
            ds.Vb_pine[i]   = float(format(VOLUME[2], '.2f'))
            ds.Vb_birch[i]  = float(format(VOLUME[3], '.2f'))
            ds.Vb_others[i] = float(format(VOLUME[4], '.2f'))
            ds.Vb_ros[i]    = float(format(VOLUME[5], '.2f'))
            ds.Vb_warm[i]   = float(format(VOLUME[6], '.2f'))
            
            ds.Initial_BGB_living[i]           = float(format(self.plot.fCO(**ds0)[0],'.2f'))
            ds.Initial_co2_living[i]           = float(format(self.plot.fCO(**ds0)[1],'.2f')) 
            ds.Initial_biomass_living[i]       = float(format(self.plot.fCO(**ds0)[2],'.2f'))            
            ds.Initial_carbon_living[i]        = float(format(self.plot.fCO(**ds0)[3],'.2f'))
            ds.Initial_carbon_stems_living[i]  = float(format(self.plot.fCO(**ds0)[4],'.2f'))
            ds.Initial_carbon_roots_living[i]  = float(format(self.plot.fCO(**ds0)[5],'.2f'))
            ds.Initial_co2_stems_living[i]     = float(format(self.plot.fCO(**ds0)[6],'.2f'))
            ds.Initial_co2_roots_living[i]     = float(format(self.plot.fCO(**ds0)[7],'.2f'))
            
            
            ds.MIC_no[i] = self.scenario
            
            if ds.Nb[i] !=0:
                No_managed_tuple    = self.No_management(i, ds, ds0, Clear_cut_tag, seed_tree_cut_tag,Thinn_MS_tag,Thinn_MP_tag,Thinn_HS_tag,Thinn_HP_tag,Thinn_LS_tag, fertilization, Site_prep_after_harvesting)
                Clear_cut_tag       = No_managed_tuple[0]
                seed_tree_cut_tag   = No_managed_tuple[1]
                #ds.MIC_no[i]        = float(format(No_managed_tuple[2], "d"))
                ds.mgt[i]           = No_managed_tuple[2]
                
                """
                Implentation of Thinning
                
                """
                Thinn_tuple         = self.Thinn_implementation(i, ds, ds0, Number_Thinn)
                Thinn_MS_tag        = Thinn_tuple[0]
                Thinn_MP_tag        = Thinn_tuple[1] 
                Thinn_HS_tag        = Thinn_tuple[2] 
                Thinn_HP_tag        = Thinn_tuple[3]
                Thinn_LS_tag        = Thinn_tuple[4]
                Thinn_BL_tag        = Thinn_tuple[5]
                #Minimum_harvest_age = Thinn_tuple[5] 
                Thinn_age           = Thinn_tuple[6] 
                ds.mgt[i]           = Thinn_tuple[7] 
                ds.Nr[i]            = float(format(Thinn_tuple[8],'.2f')) 
                ds.Gr[i]            = float(format(Thinn_tuple[9],'.2f'))
                #ds.MIC_no[i]        =  float(format(Thinn_tuple[10], 'd'))
                Product_tag_thinn   = Thinn_tuple[10]
                ds.Vr_tot[i]        = float(format(Thinn_tuple[11],'.2f'))
                ds.Vr_spruce[i]     = float(format(Thinn_tuple[12],'.2f'))
                ds.Vr_pine[i]       = float(format(Thinn_tuple[13],'.2f'))
                ds.Vr_birch[i]      = float(format(Thinn_tuple[14],'.2f'))
                ds.Vr_others[i]     = float(format(Thinn_tuple[15],'.2f'))
                ds.Vr_ros[i]        = float(format(Thinn_tuple[16],'.2f'))
                ds.Vr_warm[i]       = float(format(Thinn_tuple[17],'.2f'))
                
                ds.R_BGB[i]         = float(format(Thinn_tuple[18],'.2f'))
                ds.R_co2[i]         = float(format(Thinn_tuple[19],'.2f'))
                ds.R_biomass[i]     = float(format(Thinn_tuple[20],'.2f'))
                ds.R_carbon[i]      = float(format(Thinn_tuple[21],'.2f'))
                ds.R_carbon_stems[i]= float(format(Thinn_tuple[22],'.2f'))
                ds.R_carbon_roots[i]= float(format(Thinn_tuple[23],'.2f'))
                ds.R_co2_stems[i]   = float(format(Thinn_tuple[24],'.2f'))
                ds.R_co2_roots[i]   = float(format(Thinn_tuple[25],'.2f'))
                
                Number_Thinn        = Thinn_tuple[26]
                
                
                
                """
                Timber products (Saw timber & pulpwood)
                
                """                
                
                if Product_tag_thinn  == True:
                    
                    Timber_products_tuple = self.plot.fProducts(i)  
                    
                    ds.R_SSaw[i]  = float(format(Timber_products_tuple[0],'.2f'))
                    ds.R_SPulp[i] = float(format(Timber_products_tuple[1],'.2f'))
                    ds.R_PSaw[i]  = float(format(Timber_products_tuple[2],'.2f'))
                    ds.R_PPulp[i] = float(format(Timber_products_tuple[3],'.2f'))
                    ds.R_HSaw[i]  = float(format(Timber_products_tuple[4],'.2f'))
                    ds.R_HPulp[i] = float(format(Timber_products_tuple[5],'.2f'))
                    
                                      
                
                """
                Implentation of fertilization
                
                """                
                
                
                fertilization_tuple = self.Fertilization_implementation(i , ds, ds0,Thinn_HS_tag,Thinn_HP_tag, Thinn_age,fertilization)
                fertilization       = fertilization_tuple[0] 
                #ds.MIC_no[i]        = float(format(fertilization_tuple[1] , 'd'))
                ds.Vra[i]           = float(format(fertilization_tuple[1],'.2f'))
                ds.mgt[i]           = fertilization_tuple[2]
                
                """
                Implentation of clear cut
                
                """  
                 
                ClearCut_tuple              = self.ClearCut_Implementation(i , ds, ds0, Thinn_MS_tag,Thinn_LS_tag,Thinn_HS_tag,Thinn_HP_tag,Thinn_BL_tag, self.Harvest_age, Thinn_age, fertilization, Clear_cut_tag, Next_Rotation_age, Site_prep_after_harvesting, Establishment_age)
                Clear_cut_tag               = ClearCut_tuple[0]
                Site_prep_after_harvesting  = ClearCut_tuple[1]
                #ds.MIC_no[i]        = float(format(ClearCut_tuple[2] , 'd')) 
                Next_Rotation_age           = ClearCut_tuple[2]
                ds.mgt[i]                   = ClearCut_tuple[3]
                ds.Nr[i]                    = float(format(ClearCut_tuple[4],'.2f'))
                ds.Gr[i]                    = float(format(ClearCut_tuple[5],'.2f'))
                Establishment_age           = ClearCut_tuple[6]
                Product_tag_cc              = ClearCut_tuple[7]
                
                ds.Vr_tot[i]                = float(format(ClearCut_tuple[8],'.2f'))
                ds.Vr_spruce[i]             = float(format(ClearCut_tuple[9],'.2f'))
                ds.Vr_pine[i]               = float(format(ClearCut_tuple[10],'.2f'))
                ds.Vr_birch[i]              = float(format(ClearCut_tuple[11],'.2f'))
                ds.Vr_others[i]             = float(format(ClearCut_tuple[12],'.2f'))
                ds.Vr_ros[i]                = float(format(ClearCut_tuple[13],'.2f'))
                ds.Vr_warm[i]               = float(format(ClearCut_tuple[14],'.2f'))
                
                ds.R_BGB[i]                 = float(format(ClearCut_tuple[15],'.2f'))
                ds.R_co2[i]                 = float(format(ClearCut_tuple[16],'.2f'))
                ds.R_biomass[i]             = float(format(ClearCut_tuple[17],'.2f'))
                ds.R_carbon[i]              = float(format(ClearCut_tuple[18],'.2f'))
                ds.R_carbon_stems[i]        = float(format(ClearCut_tuple[19],'.2f'))
                ds.R_carbon_roots[i]        = float(format(ClearCut_tuple[20],'.2f'))
                ds.R_co2_stems[i]           = float(format(ClearCut_tuple[21],'.2f'))
                ds.R_co2_roots[i]           = float(format(ClearCut_tuple[22],'.2f'))
                """
                Timber products (Saw timber & pulpwood)
                
                """                
                
                if Product_tag_cc  == True:
                    
                    Timber_products_tuple = self.plot.fProducts(i)  


                    ds.R_SSaw[i]  = float(format(Timber_products_tuple[0],'.2f'))  
                    ds.R_SPulp[i] = float(format(Timber_products_tuple[1],'.2f')) 
                    ds.R_PSaw[i]  = float(format(Timber_products_tuple[2],'.2f')) 
                    ds.R_PPulp[i] = float(format(Timber_products_tuple[3],'.2f')) 
                    ds.R_HSaw[i]  = float(format(Timber_products_tuple[4],'.2f')) 
                    ds.R_HPulp[i] = float(format(Timber_products_tuple[5],'.2f'))
                    
                    
                    # ds.Dead_wood_co2[i]      = float(format(self.plot.fDeadtrees()[0],'.2f'))
                    # ds.Dead_wood_biomass[i]  = float(format(self.plot.fDeadtrees()[1],'.2f'))
                    # ds.Dead_wood_carbon[i] = float(format(self.plot.fDeadtrees()[2],'.2f'))
                
                
                if Clear_cut_tag  == True and ds.t[i] >= Establishment_age:
                    RegenMethod_tuple1 = self.Regeneration_implementation(i, ds, ds0, Clear_cut_tag, seed_tree_cut_tag) 
                    Clear_cut_tag     = RegenMethod_tuple1[0]
                    seed_tree_cut_tag = RegenMethod_tuple1[1]
                    

                """
                Implentation of seed tree cut
                
                """
                    
                seed_tree_cut_tuple = self.seed_tree_cut_Implementation(i ,ds, ds0,Thinn_MP_tag, Thinn_HP_tag, self.Harvest_age, Thinn_age, fertilization , Next_Rotation_age, seed_tree_cut_tag, Site_prep_after_harvesting, Establishment_age)
                seed_tree_cut_tag   = seed_tree_cut_tuple[0]
                Site_prep_after_harvesting = seed_tree_cut_tuple[1]
                Next_Rotation_age   = seed_tree_cut_tuple[2]
                ds.mgt[i]           = seed_tree_cut_tuple[3]
                ds.Nr[i]            = float(format(seed_tree_cut_tuple[4],'.2f'))
                ds.Gr[i]            = float(format(seed_tree_cut_tuple[5],'.2f'))
                #ds.MIC_no[i]        = float(format(seed_tree_cut_tuple[6] , 'd') 
                Establishment_age   = seed_tree_cut_tuple[6]
                Product_tag_sc      = seed_tree_cut_tuple[7]
                ds.Vr_tot[i]        = float(format(seed_tree_cut_tuple[8],'.2f'))
                ds.Vr_spruce[i]     = float(format(seed_tree_cut_tuple[9],'.2f'))
                ds.Vr_pine[i]       = float(format(seed_tree_cut_tuple[10],'.2f'))
                ds.Vr_birch[i]      = float(format(seed_tree_cut_tuple[11],'.2f'))
                ds.Vr_others[i]     = float(format(seed_tree_cut_tuple[12],'.2f'))
                ds.Vr_ros[i]        = float(format(seed_tree_cut_tuple[13],'.2f'))
                ds.Vr_warm[i]       = float(format(seed_tree_cut_tuple[14],'.2f'))
                
                ds.R_BGB[i]         = float(format(seed_tree_cut_tuple[15],'.2f'))
                ds.R_co2[i]         = float(format(seed_tree_cut_tuple[16],'.2f'))
                ds.R_biomass[i]     = float(format(seed_tree_cut_tuple[17],'.2f'))
                ds.R_carbon[i]      = float(format(seed_tree_cut_tuple[18],'.2f'))
                ds.R_carbon_stems[i]= float(format(seed_tree_cut_tuple[19],'.2f'))
                ds.R_carbon_roots[i]= float(format(seed_tree_cut_tuple[20],'.2f'))
                ds.R_co2_stems[i]   = float(format(seed_tree_cut_tuple[21],'.2f'))
                ds.R_co2_roots[i]   = float(format(seed_tree_cut_tuple[22],'.2f'))
                
                """
                Timber products (Saw timber & pulpwood)
                
                """
                if Product_tag_sc  == True:
                    
                    Timber_products_tuple = self.plot.fProducts(i) 
                    
                    ds.R_SSaw[i]  = float(format(Timber_products_tuple[0],'.2f')) 
                    ds.R_SPulp[i] = float(format(Timber_products_tuple[1],'.2f')) 
                    ds.R_PSaw[i]  = float(format(Timber_products_tuple[2],'.2f')) 
                    ds.R_PPulp[i] = float(format(Timber_products_tuple[3],'.2f')) 
                    ds.R_HSaw[i]  = float(format(Timber_products_tuple[4],'.2f')) 
                    ds.R_HPulp[i] = float(format(Timber_products_tuple[5],'.2f'))

                    
                    # ds.Dead_wood_co2[i]      = float(format(self.plot.fDeadtrees()[0],'.2f'))
                    # ds.Dead_wood_biomass[i]  = float(format(self.plot.fDeadtrees()[1],'.2f'))
                    # ds.Dead_wood_carbon[i] = float(format(self.plot.fDeadtrees()[2],'.2f'))                
                
                
                
                if seed_tree_cut_tag  == True and ds.t[i] >= Establishment_age:
                    RegenMethod_tuple2  = self.Regeneration_implementation(i, ds, ds0, Clear_cut_tag, seed_tree_cut_tag)
                    Clear_cut_tag     = RegenMethod_tuple2[0]
                    seed_tree_cut_tag = RegenMethod_tuple2[1] 

            
            Dead_wood_tuple       = self.plot.deadwood_decay_mass() 

            ds.Dead_wood_co2[i]      = float(format(Dead_wood_tuple[0],'.2f'))
            ds.Dead_wood_carbon[i]   = float(format(Dead_wood_tuple[1],'.2f'))
            

            """
                ###================================================================================================================================================================
                ### Biodiversity Indicator                                         definition                      100 points                  50 points             0 points
                ###================================================================================================================================================================        
                ### Species richness                             | # of species present in that plot   |         all species(>=4)               = 3                  <= 2
                ###----------------------------------------------------------------------------------------------------------------------------------------------------------------        
                ### Species diversity (Shannon Index) alpha      | combines species richness and evenness|            >= 1                  <1 and >= 0.5            > 0.5
                ###----------------------------------------------------------------------------------------------------------------------------------------------------------------        
                ### amount of deadwood                          |   Volume (m3/ha)   |                               > 20 m3/ha           <= 20 and >=5 m3/ha         < 5
                ###----------------------------------------------------------------------------------------------------------------------------------------------------------------        
                ### amount of large deciduous trees other than birch  |   Volume (m3/ha)   |                          > 50 m3/ha           <= 50 and >=10 m3/ha         < 10
                ###----------------------------------------------------------------------------------------------------------------------------------------------------------------        
                ### number of large trees                      |   N/ha  |                                          tree > 40cm dbh             tree > 30cm dbh       not present
                ###----------------------------------------------------------------------------------------------------------------------------------------------------------------        
                ### mature broadleaf-rich forest              |if the forest is older than 80 yrs    
                ###                                and at least 25% of the basal area is decidous trees| 
            """   
            
            Dead_wood_vol_tuple     = self.plot.deadwood_decay_vol(volume_deadwood_p0) 

            Volume_deadwood         = float(format(Dead_wood_vol_tuple[0],'.2f'))
            BI3                     = Dead_wood_vol_tuple[2]
            volume_deadwood_p0      = float(format(Dead_wood_vol_tuple[3],'.2f'))
#            ds.NoDecayDead[i]        = Dead_wood_vol_tuple[3]
            ds.Deadwood[i]          = Volume_deadwood
                                  
            
            ds.Richness[i]          = float(format(self.plot.species_richness()[0],'.2f'))
            BI1                     = self.plot.species_richness()[1]
            
            
            ds.Shannon[i]           = float(format(self.plot.calc_alpha()[0],'.2f'))
            BI2                     = self.plot.calc_alpha()[1]
 
            
            ds.Lsize_deciduous[i]   = float(format(self.plot.large_decidous_vol()[0],'.2f'))
            BI4                     = self.plot.large_decidous_vol()[1]
            
            
            ds.Lsize_All[i]         = float(format(self.plot.large_trees()[0],'.2f'))
            BI5                     = self.plot.large_trees()[1] 
            
            Biodiversity_points = [BI1 , BI2  , BI3 , BI4 , BI5]
            bio_points = np.array(Biodiversity_points, dtype=float)
            bio_point = np.mean(bio_points)
            
            ds.biodiversity[i] = BI1 + BI2  + BI3 + BI4 + BI5
            ds.BI1[i]  = BI1
            ds.BI2[i]  = BI2
            ds.BI3[i]  = BI3
#            Simulator.GROWTH1.append((i,ds.NoDecayDead[i], ds.BI3[i]))
            ds.BI4[i]  = BI4
            ds.BI5[i]  = BI5
            
            
            if ds.R_carbon[i] != 0:
                ds.Dead_wood_carbon[i]  = float(format(ds.Dead_wood_carbon[i] + ds.carbon_roots[i],'.2f'))  
            else:
                ds.Dead_wood_carbon[i]  = float(format(ds.Dead_wood_carbon[i],'.2f'))    
                
            if ds.R_co2[i] != 0:     
                ds.Dead_wood_co2[i]     = float(format(ds.Dead_wood_co2[i] + ds.co2_roots[i],'.2f'))  
            else:
                 ds.Dead_wood_co2[i]     =  float(format(ds.Dead_wood_co2[i],'.2f'))    
            
#            ds.Dead_wood_biomass[i] = float(format(ds.Dead_wood_biomass[i] ,'.2f'))  
            
            if (ds.Nr[i] > 0): ds.tst[i] = 0
            ds.Na[i] = float(format(ds.Nb[i] - ds.Nr[i],'.2f'))             
            
            ds.Ga[i] = float(format(ds.Gb[i] - ds.Gr[i],'.2f'))  
            
            if ds.Na[i] > 0:
                ds.Gr_stock[i]        = float(format(self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[0],'.2f'))   ## Growing_stock total after  
                ds.Gr_stock_spruce[i] = float(format(self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[1],'.2f'))   ## Growing_stock spruce
                ds.Gr_stock_pine[i]   = float(format(self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[2],'.2f'))  ## Growing_stock pine
                ds.Gr_stock_birch[i]  = float(format(self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[3],'.2f'))   ## Growing_stock birch
                ds.Gr_stock_others[i] = float(format(self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[4],'.2f'))   ## Growing_stock others
                ds.Gr_stock_ros[i]    = float(format(self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[5],'.2f'))   ## Growing_stock ros
                ds.Gr_stock_warm[i]   = float(format(self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[6],'.2f'))   ## Growing_stock warm
                
                ds.Va[i]              = float(format(self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[0],'.2f'))   ## Growing_stock total after
            
            if ds.Nr[i] == 0:            
                ds.Vr_tot[i]        = 0. 
                ds.Vr_spruce[i]     = 0. 
                ds.Vr_pine[i]       = 0. 
                ds.Vr_birch[i]      = 0. 
                ds.Vr_others[i]     = 0. 
                ds.Vr_ros[i]        = 0. 
                ds.Vr_warm[i]       = 0. 
                
            
            """
            update the plot age if we have clearcut or seed tree cut
            """
            #ds.t[i] = (self.p - 1) * self.prescription.interval + "self.plot.t"  + self.prescription.interval
            
            ## PAI = (volume at the end of a period- volume at the beginning of a period)/length of the period  
            ds.Vra[i] += ds.Vr_tot[i] + ds0['Vra']
            ds.Vra[i]  = float(format(ds.Vra[i],'.2f')) 
            ds.PAI[i] = float(format((((ds.Vra[i] + ds.Gr_stock[i])-(ds0['Vra'] + ds0['Gr_stock'])) / ds0['interval']),'.2f'))  
            
            """
            update the stand carbon and co2 if we have clearcut or seed tree cut or thinning
            * Carbon living include carbon stems and carbon roots
            """
        
            ds.co2_living[i]           = float(format(self.plot.fCO()[1],'.2f')) 
            ds.biomass_living[i]       = float(format(self.plot.fCO()[2],'.2f'))            
            ds.carbon_living[i]        = float(format(self.plot.fCO()[3],'.2f'))
            ds.carbon_stems[i]         = float(format(self.plot.fCO()[4],'.2f'))
            ds.carbon_roots[i]         = float(format(self.plot.fCO()[5],'.2f'))
            ds.co2_stems[i]            = float(format(self.plot.fCO()[6],'.2f'))
            ds.co2_roots[i]            = float(format(self.plot.fCO()[7],'.2f'))
            
            """
            soil carbon (soil, trees, roots,..)
            """
            ds.soilC[i] = float(format(self.plot.fSoilCarbon(),'.2f')) 
            
            """
            Total carbon stock (soil, trees, roots, stumps, dead wood)
            Total carbon stock = carbon living + deadwood carbon + soil carbon
            """
            
            ds.Total_carbon_stock[i] =  float(format(ds.carbon_living[i] + ds.Dead_wood_carbon[i] + ds.soilC[i],'.2f'))  
            
            ds0 = ds.loc[i]
            
            ds["new_mic"] = "." + ds["MIC_no"].astype(str) + str(self.unique)
            ds["new_p"]   = "." + ds["p"].astype(str)
            ds["plot_id.MIC_no.p"] = ds["plot_id"].astype(str) + ds["new_mic"].astype(str)+ ds["new_p"].astype(str)
            ds["plot_id.MIC_no"] = ds["plot_id"].astype(str) + ds["new_mic"].astype(str)
                      
            
        #This neatly allocate all columns and rows to a .csv file
##       ds.to_csv(os.path.join(outputfolder, "name.csv"), index = False)
        #ds.to_csv(os.path.join(self.input,'%s.DataFrame.csv'%(self.name)), mode= 'a', index = False, header= False)
        
                                                    # %%%%%          output format            %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        
        dsMgt = ds[ds["mgt"] == "-1"]
        dfGE_15_MIC_no = dfGE_15["MIC_no"].unique().tolist()
        df10_15 = self.prescription.management[self.prescription.management['Site index'] == "10.5-15.5"]
        df10_15_MIC_no = df10_15["MIC_no"].unique().tolist()
        dfL_10 = self.prescription.management[self.prescription.management['Site index'] == "L_10.5"]
        dfL_10_MIC_no = dfL_10["MIC_no"].unique().tolist()
        
        Mgtstore = []
        PLTMgtstore = []
        Mgtstore = ds["mgt"].unique().tolist()
        

        if len(Mgtstore) > 1 and -1 in Mgtstore:
            dsMgt = ds[ds["mgt"] != -1]
            PLTMgtstore = dsMgt["plot_id.MIC_no"].unique().tolist()
            
        #This neatly allocate all columns and rows to a .txt file
        use_cols= ['plot_id.MIC_no.p','plot_id','mgt','t','Year', 'H0','Na','Ga','Gr_stock','Gr_stock_spruce','Gr_stock_pine', 'Gr_stock_birch', 'Gr_stock_others', 'Gr_stock_ros','Gr_stock_warm',
                                              'Vb','Vb_spruce' , 'Vb_pine'  ,'Vb_birch' , 'Vb_others' , 'Vb_ros' , 'Vb_warm', 'Vr_tot','Vr_spruce','Vr_pine',
                                              'Vr_birch','Vr_others','Vr_ros','Vr_warm', 'Total_carbon_stock','carbon_living','carbon_stems','carbon_roots', 
                                              'R_carbon','R_carbon_stems','R_carbon_roots','Dead_wood_carbon','R_SPulp','R_SSaw','R_PPulp', 'R_PSaw','R_HPulp','R_HSaw','soilC', 
                                              'biodiversity', 'BI1', 'BI2', 'BI3','BI4', 'BI5','Richness','Shannon','Deadwood','Lsize_deciduous','Lsize_All']
        
        
        
        with open(os.path.join(self.output,'%s.txt'%(self.plot.plot_id)),'a') as outfile:
            
            ds.to_string(outfile,header = False , index = False ,columns = use_cols) 
            outfile.write('\n')

            
        fexp=open(os.path.join(self.output_Mgt,'%s.txt'%("Plots_Mgt")),'a')
        for t in PLTMgtstore:
            line=''.join(str(x) for x in t)
            fexp.write(line+'\n')
        fexp.close()
                           
        return ds.reindex(columns=columns)        

    
                                                # %%%%%%      Management alternative implementation     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
    
    
                                                # %%%%%         Thinning           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


    def Thinn_implementation(self,i, ds_, ds0_, Number_Thinn_):
        
        """
        """
        Number_Thinn = Number_Thinn_
        ds = ds_
        ds0 = ds0_
        ## we do not use the fertilization tag in thinning but for further understand for readers we decided to add it here

        dfGE_15 = self.prescription.management[self.prescription.management['Site index'] == "GE_15.5"]
        dfGE_15_thin = dfGE_15[dfGE_15["Thinn"] == "thin"]
        df10_15 = self.prescription.management[self.prescription.management['Site index'] == "10.5-15.5"]
        df10_15_thin = df10_15[df10_15["Thinn"] == "thin"]
        dfL_10 = self.prescription.management[self.prescription.management['Site index'] == "L_10.5"]            
            
        MIC_GE15_Thinn =[]
        for idx,row in dfGE_15_thin.iterrows():
            MIC_GE15_Thinn.append(row["MIC_type"])
        MIC_10_15_Thinn =[]
        for idx,row in df10_15_thin.iterrows():
            MIC_10_15_Thinn.append(row["MIC_type"])               
#       self.GROWTH1.append(Gb)
            
        if __SI__ == 26:              
            Minimum_Thinning_age = 30
            Minimum_harvest_age  = 40

        elif __SI__ == 23:
            Minimum_Thinning_age = 35
            Minimum_harvest_age  = 45

        elif __SI__ == 20:
            Minimum_Thinning_age = 35
            Minimum_harvest_age  = 50

        elif __SI__ == 17:
            Minimum_Thinning_age = 45
            Minimum_harvest_age  = 60

        elif __SI__ == 14:
            Minimum_Thinning_age = 55
            Minimum_harvest_age  = 70
 
        elif __SI__ == 11 or __SI__ == 12:
            Minimum_Thinning_age = 60
            Minimum_harvest_age  = 80

        elif __SI__ == 8:
            Minimum_Thinning_age = 0
            Minimum_harvest_age  = 85

        elif __SI__ == 7:
            Minimum_Thinning_age = 0
            Minimum_harvest_age  = 90

        else:
            Minimum_Thinning_age = 0
            Minimum_harvest_age  = 95

                

        Thinn_MS_tag = False
        Thinn_MP_tag = False
        Thinn_HS_tag = False
        Thinn_HP_tag = False
        Thinn_LS_tag = False
        Thinn_BL_tag = False
        Product_tag_thinn  = False          
                   
        if (ds.t[i] >= Minimum_Thinning_age) and (__SI__ >= 15.5)  and (ds.MIC_no[i] in [1,3,5,6,8,10]) and (ds.mic_type[i] in MIC_GE15_Thinn) and (ds.Gb[i] >= 35) and (ds.H0[i] >= 12) and (ds.H0[i] <= 15) and (Number_Thinn <= 2) :
            # it defines the thinning period
            this_period = ds.p[i] 
            if ds.mic_type[i] == "High_pine" or ds.mic_type[i] == "Medium_pine":
                if ds.mic_type[i] == "High_pine":
                    Thinn_HP_tag = True
                    fertilization = False
                    #ds.MIC_no[i] = 3
                else:
                    Thinn_MP_tag = True
                    #ds.MIC_no[i] = 5
                        
                ds.mgt[i] =self.mgt["thin"]
                # this defines thinning ratio
                Gr0 = ds.Gb[i] - 22   # 22 is the minimum basal area after thinning               
                TR_ =  (Gr0 / ds.Gb[i])
                G_b = ds.Gb[i]
                
                self.prescription.add_thin(this_period, TI= 35 , TR= TR_)
                Thinn_age = ds.t[i]
                ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                Removed_trees = ds.Nr[i]
                R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                
                R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 

                R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100    
                
                
                mic_tp = ds.mic_type[i]
                
                """ this line is to remove the trees required in thinning and update the objects """                
                self.plot.fR_Thinn(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots, 
                                    G_b, R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,
                                    R_vol_ros,R_vol_warm, mic_tp,  ds.Year[i], ds.p[i], "thinning")
                Product_tag_thinn  = True
                Number_Thinn += 1
                
                ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i, **ds0)),'.2f'))
                
                ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
            
            
                ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                
            else:
                if ds.mic_type[i] == "High_spruce":
                    Thinn_HS_tag = True
                    fertilization = False
                    #ds.MIC_no[i] = 8
                else:
                    Thinn_MS_tag = True
                    #ds.MIC_no[i] = 10
                ds.mgt[i] = self.mgt["thin"]
                # this defines thinning ratio
                Gr0 = ds.Gb[i] - 24   # 22 is the minimum basal area after thinning           
                TR_ =  (Gr0 / ds.Gb[i])
                G_b = ds.Gb[i]    
                self.prescription.add_thin(this_period, TI= 35 , TR= TR_)
                    
                ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                Removed_trees = ds.Nr[i]              
                R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                
                R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                
                mic_tp = ds.mic_type[i]
                
                
                """ this line is to remove the trees required in thinning and update the objects """
                
                self.plot.fR_Thinn(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots, 
                                    G_b, R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,
                                    R_vol_ros,R_vol_warm,mic_tp , ds.Year[i], ds.p[i], "thinning")
                Product_tag_thinn  = True
                Number_Thinn += 1
                
                Thinn_age = ds.t[i]
                ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                
                ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                
                ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f') ) 
                ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                

                    
        elif (ds.t[i] >= Minimum_Thinning_age) and (__SI__ < 15.5) and (__SI__ >= 10.5 ) and (ds.MIC_no[i] in [1,3,5,6,8,10]) and (ds.mic_type[i] in MIC_10_15_Thinn) and (ds.Gb[i] >= 35) and (ds.H0[i] >= 12) and (ds.H0[i] <= 15) and (Number_Thinn <= 2) :   
            this_period = ds.p[i] 
            if ds.mic_type[i] == "High_pine":
                Thinn_HP_tag = True
                fertilization = False
                #ds.MIC_no[i] = 3
                
            elif ds.mic_type[i] == "Medium_pine":
                Thinn_MP_tag = True
                #ds.MIC_no[i] = 5 
            elif ds.mic_type[i] == "High_spruce":
                Thinn_HS_tag = True
                fertilization = False
                #ds.MIC_no[i] = 8
            else:
                
                Thinn_MS_tag = True
                #ds.MIC_no[i] = 10
                
            ds.mgt[i] = self.mgt["thin"]
            # this defines thinning ratio
            Gr0 = ds.Gb[i] - 20   # 22 is the minimum basal area after thinning           
            TR_ =  (Gr0 / ds.Gb[i])
            G_b = ds.Gb[i]
            self.prescription.add_thin(this_period, TI= 35 , TR= TR_)
            ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
            Removed_trees = ds.Nr[i]
            R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
            R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
            R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
            R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
            R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
            R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
            R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
            R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100  
                
            R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
            R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
            R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
            R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
            R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
            R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
            R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
            R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
            
            mic_tp = ds.mic_type[i]
            
            """ this line is to remove the trees required in thinning and update the objects """               
            self.plot.fR_Thinn(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots, 
                                G_b, R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,
                                R_vol_ros,R_vol_warm, mic_tp ,ds.Year[i], ds.p[i], "thinning")
            Product_tag_thinn  = True
            Number_Thinn += 1
            
            ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
            
            ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
            ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
            ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
            ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
            ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
            ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
            ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
            
            ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
            ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
            ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
            ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
            ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
            ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
            ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
            ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))


            Thinn_age = ds.t[i]
        else:
            ds.Nr[i]               = 0.
            ds.Gr[i]               = 0.
            Thinn_age              = 0.
            ds.Vr_tot[i]           = 0.
            ds.Vr_spruce[i]        = 0.
            ds.Vr_pine[i]          = 0.
            ds.Vr_birch[i]         = 0.
            ds.Vr_others[i]        = 0.
            ds.Vr_ros[i]           = 0.
            ds.Vr_warm[i]          = 0.
            ds.R_BGB[i]            = 0.
            ds.R_co2[i]            = 0.
            ds.R_biomass[i]        = 0.
            ds.R_carbon[i]         = 0.
            ds.R_carbon_stems[i]   = 0.
            ds.R_carbon_roots[i]   = 0.
            ds.R_co2_stems[i]      = 0.
            ds.R_co2_roots[i]      = 0.
            
        return Thinn_MS_tag,Thinn_MP_tag,Thinn_HS_tag,Thinn_HP_tag,Thinn_LS_tag, Thinn_BL_tag, Thinn_age, ds.mgt[i], ds.Nr[i], ds.Gr[i], \
        Product_tag_thinn, ds.Vr_tot[i], ds.Vr_spruce[i], ds.Vr_pine[i], ds.Vr_birch[i], ds.Vr_others[i], ds.Vr_ros[i], ds.Vr_warm[i], ds.R_BGB[i], \
        ds.R_co2[i], ds.R_biomass[i], ds.R_carbon[i] , ds.R_carbon_stems[i],ds.R_carbon_roots[i],ds.R_co2_stems[i] , ds.R_co2_roots[i], Number_Thinn


 # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%          Fertilization           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 


    def Fertilization_implementation(self,i , ds_, ds0_,Thinn_HS_tag,Thinn_HP_tag,Thinn_age,fertilization):
        
        """
        Fertilization should be implemented 5 years after thinning and just once
         "Site_prep":4, "Fertilization":5
        
        """

        ds = ds_
        ds0 = ds0_
        
        five_yrs_after = 5

            
        dfGE_15 = self.prescription.management[self.prescription.management['Site index'] == "GE_15.5"]
        df10_15 = self.prescription.management[self.prescription.management['Site index'] == "10.5-15.5"]
        dfL_10 = self.prescription.management[self.prescription.management['Site index'] == "L_10.5"] 
            
        dfGE_15_fertilization =  dfGE_15[dfGE_15["Fertilization"] == "yes"]
        df10_15_fertilization =  df10_15[df10_15["Fertilization"] == "yes"]
        dfL_10_fertilization  =  dfL_10 [dfL_10 ["Fertilization"] == "yes"]  
            
        MIC_GE15_Ferti =[]
        for idx,row in dfGE_15_fertilization.iterrows():
            MIC_GE15_Ferti.append(row["MIC_type"])

        MIC_10_15_Ferti =[]
        for idx,row in df10_15_fertilization.iterrows():
            MIC_10_15_Ferti.append(row["MIC_type"]) 

        MIC_L10_Ferti =[]
        for idx,row in dfL_10_fertilization.iterrows():
            MIC_L10_Ferti.append(row["MIC_type"])  
                
        if (ds.t[i] >= Thinn_age + five_yrs_after ) and (__SI__ >= 15.5) and (ds.MIC_no[i] in [1,6]) and (ds.mic_type[i] in MIC_GE15_Ferti) and fertilization == False:
                
            if ds.mic_type[i] == "High_pine" and (Thinn_HP_tag == True):
                #ds.MIC_no[i] = 1
                fertilization = True
                this_period = ds.p[i]
                                 
                ds.Vra[i] += ds.Vr[i] + ds0['Vra']
                ## PAI = (volume at the end of a period- volume at the beginning of a period)/length of the period            
                PAI_ = (((ds.Vra[i] + ds.Vb[i])- (ds0['Vra'] + ds0['Vb'])) / ds0['interval'])
                 
                stand_age = ds.t[i]
                ALTITUDE = self.plot.Altitude
                SI = self.plot.H40
                Latitude = self.plot.LATITUDE
                ds.mgt[i] = self.mgt["Fertilization"] 
                 
                self.plot.Fertilization_Rosvall(PAI_,stand_age,ALTITUDE,SI,Latitude, ds.Year[i], ds.p[i], "Fertilization",  **ds0)
                
                                   
                    
            elif ds.mic_type[i] == "High_spruce" and (Thinn_HS_tag == True):
                #ds.MIC_no[i] = 6                
                fertilization = True
                this_period = ds.p[i]
                    
                ds.Vra[i] += ds.Vr[i] + ds0['Vra']
                ## PAI = (volume at the end of a period- volume at the beginning of a period)/length of the period            
                PAI_ = (((ds.Vra[i] + ds.Vb[i])- (ds0['Vra'] + ds0['Vb'])) / ds0['interval'])
                 
                stand_age = ds.t[i]
                ALTITUDE = self.plot.Altitude
                SI = self.plot.H40
                Latitude = self.plot.LATITUDE
                ds.mgt[i] = self.mgt["Fertilization"] 
                 
                self.plot.Fertilization_Rosvall(PAI_,stand_age,ALTITUDE,SI,Latitude, ds.Year[i], ds.p[i], "Fertilization", **ds0)
                
            else:
                fertilization = False
 
        elif (ds.t[i] >= Thinn_age + five_yrs_after ) and (__SI__ < 15.5) and (__SI__ >= 10.5 ) and (ds.MIC_no[i] in [1,6]) and (ds.mic_type[i] in MIC_10_15_Ferti) and fertilization == False:
                
            if ds.mic_type[i] == "High_pine" and (Thinn_HP_tag == True):
                fertilization = True
                this_period = ds.p[i]
                #ds.MIC_no[i] = 1
                ds.Vra[i] += ds.Vr[i] + ds0['Vra']
                ## PAI = (volume at the end of a period- volume at the beginning of a period)/length of the period            
                PAI_ = (((ds.Vra[i] + ds.Vb[i])- (ds0['Vra'] + ds0['Vb'])) / ds0['interval'])
              
                stand_age = ds.t[i]
                ALTITUDE = self.plot.Altitude
                SI = self.plot.H40
                Latitude = self.plot.LATITUDE
                ds.mgt[i] = self.mgt["Fertilization"] 
                self.plot.Fertilization_Rosvall(PAI_,stand_age,ALTITUDE,SI,Latitude, ds.Year[i], ds.p[i], "Fertilization", **ds0)
                
                
                    
            elif ds.mic_type[i] == "High_spruce" and (Thinn_HS_tag == True):
                fertilization = True
                this_period = ds.p[i]
                #ds.MIC_no[i] = 6                 
                ds.Vra[i] += ds.Vr[i] + ds0['Vra']
                ## PAI = (volume at the end of a period- volume at the beginning of a period)/length of the period            
                PAI_ = (((ds.Vra[i] + ds.Vb[i]) - (ds0['Vra'] + ds0['Vb'])) / ds0['interval'])
              
                stand_age = ds.t[i]
                ALTITUDE = self.plot.Altitude
                SI = self.plot.H40
                Latitude = self.plot.LATITUDE 
                ds.mgt[i] = self.mgt["Fertilization"]                                 
                self.plot.Fertilization_Rosvall(PAI_,stand_age,ALTITUDE,SI,Latitude, ds.Year[i], ds.p[i], "Fertilization", **ds0) 
                
            else:                                      
                fertilization = False
                

        else:
            fertilization = False
        
        return fertilization, ds.Vra[i], ds.mgt[i]

                                                 # %%%%%%         Clear cut           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
  
    def ClearCut_Implementation(self,i , ds_, ds0_, Thinn_MS_tag,Thinn_LS_tag,Thinn_HS_tag,Thinn_HP_tag, Thinn_BL_tag , harvest_age_variable, Thinn_age, fertilization, Clear_cut_tag, Next_Rotation_age, Site_prep_after_harvesting, Establishment_age = 0):
        
        ds = ds_
        ds0 = ds0_
        
        Product_tag_cc  = False    
        if (ds.t[i] >= Thinn_age + 10):
                 
            if (ds.t[i] >= Next_Rotation_age):
                
                dfGE_15 = self.prescription.management[self.prescription.management['Site index'] == "GE_15.5"]
                df10_15 = self.prescription.management[self.prescription.management['Site index'] == "10.5-15.5"]
                dfL_10 = self.prescription.management[self.prescription.management['Site index'] == "L_10.5"] 
                
                dfGE_15_CC =  dfGE_15[dfGE_15["harvesting_method"] == "clear_cut"]
                df10_15_CC =  df10_15[df10_15["harvesting_method"] == "clear_cut"]
                dfL_10_CC  =  dfL_10 [dfL_10 ["harvesting_method"] == "clear_cut"]  
                
                MIC_GE15_CC =[]
                for idx,row in dfGE_15_CC.iterrows():
                    MIC_GE15_CC.append(row["MIC_type"])
            
                MIC_10_15_CC =[]
                for idx,row in df10_15_CC.iterrows():
                    MIC_10_15_CC.append(row["MIC_type"]) 
            
                MIC_L10_CC =[]
                for idx,row in dfL_10_CC.iterrows():
                    MIC_L10_CC.append(row["MIC_type"])            
                
                if (ds.t[i] >= harvest_age_variable) and (__SI__ >= 15.5) and (ds.MIC_no[i] in [1,6,7,8,9,10,11,12]) and (ds.mic_type[i] in MIC_GE15_CC):
                    
                    if (ds.mic_type[i] == "High_pine")  and (ds.MIC_no[i] == 1) and (Thinn_HP_tag == True) and (fertilization == True) :
                        
                        #ds.MIC_no[i] = 1
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 5
                        Establishment_age = ds.t[i] + 5
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable  + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i] 
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """                                                                  
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                            
                        # these lines should be run whether the if statement is satisfied or not
                        """ Since we have planting after the clear cut and seed tree cut, the difference can be negative. To avoid we use abs()   """
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i, after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    # if we do thinning then clear cut cannot be set before 10 years after thinning - check management alternative to find out which MIC_type need clear cut and thinning    
                    elif (ds.mic_type[i] == "Medium_spruce")  and (ds.MIC_no[i] == 9) and (Thinn_MS_tag == False) and (fertilization == False):
            
                        #ds.MIC_no[i] = 9 
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 10
                        Establishment_age = ds.t[i] + 10
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable  + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                        
                    elif (ds.mic_type[i] == "Medium_spruce")  and (ds.MIC_no[i] == 10) and (Thinn_MS_tag == True) and (fertilization == False) and (ds.t[i] >= Thinn_age + 10) :
            
                        #ds.MIC_no[i] = 10 
                        this_period = ds.p[i]
            
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 10
                        Establishment_age = ds.t[i] + 10       
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i] 
                       
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))  
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                    elif (ds.mic_type[i] == "High_spruce")  and (ds.MIC_no[i] == 8) and (Thinn_HS_tag == True) and (fertilization == True) and (ds.t[i] >= Thinn_age + 10):
            
                        #ds.MIC_no[i] = 8
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 10
                        Establishment_age = ds.t[i] + 10                    
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time+ 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                        
                    elif (ds.mic_type[i] == "High_spruce")  and (ds.MIC_no[i] == 7) and (Thinn_HS_tag == False) and (fertilization == False):
            
                        #ds.MIC_no[i] = 7
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 10
                        Establishment_age = ds.t[i] + 10                    
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))  
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f') ) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                        
                    elif (ds.mic_type[i] == "High_spruce")  and (ds.MIC_no[i] == 6) and (Thinn_HS_tag == True) and (fertilization == False) and (ds.t[i] >= Thinn_age + 10):
            
                        #ds.MIC_no[i] = 6
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 10
                        Establishment_age = ds.t[i] + 10
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                    elif (ds.mic_type[i] == "Low_spruce")  and (ds.MIC_no[i] == 11) and (Thinn_LS_tag == False) and (fertilization == False):  
            
                        #ds.MIC_no[i] = 11
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 10
                        Establishment_age = ds.t[i] + 10
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] - self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                    # No management (ds.mic_type[i] == "No_man") and (Thinn_LS_tag == False) and (fertilization == False)
                    elif (ds.mic_type[i] == "broadleaf")  and (ds.MIC_no[i] == 12) and (Thinn_BL_tag == False) and (fertilization == False):   
            
                        #ds.MIC_no[i] = 12
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                            
                                            
                elif (ds.t[i] >= harvest_age_variable) and (__SI__ < 15.5) and (__SI__ >= 10.5 ) and (ds.MIC_no[i] in [1,6,7,8,9,10,11,12]) and (ds.mic_type[i] in MIC_10_15_CC): 
                           
                    if (ds.mic_type[i] == "High_pine") and (ds.MIC_no[i] == 1) and (Thinn_HP_tag == True) and (fertilization == True) and (ds.t[i] >= Thinn_age + 10):
            
                        #ds.MIC_no[i] = 1
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 10
                        Establishment_age = ds.t[i] + 10
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
            #                   self.GROWTH1.append((this_period,ds.Nr[i]))
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                            
                    elif (ds.mic_type[i] == "Medium_spruce") and (ds.MIC_no[i] == 9) and (Thinn_MS_tag == False) and (fertilization == False):
            
                        #ds.MIC_no[i] = 9 
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                            
                    elif (ds.mic_type[i] == "Medium_spruce") and (ds.MIC_no[i] == 10) and (Thinn_MS_tag == True) and (fertilization == False) and (ds.t[i] >= Thinn_age + 10):
            
                        #ds.MIC_no[i] = 10 
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15        
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                            
                    elif (ds.mic_type[i] == "High_spruce") and (ds.MIC_no[i] == 8) and (Thinn_HS_tag == True) and (fertilization == True) and (ds.t[i] >= Thinn_age + 10):
            
                        #ds.MIC_no[i] = 8
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                            
                    elif (ds.mic_type[i] == "High_spruce") and (ds.MIC_no[i] == 7) and (Thinn_HS_tag == False) and (fertilization == False):
            
                        #ds.MIC_no[i] = 7
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6] ),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7] ),'.2f'))
                        
                    elif (ds.mic_type[i] == "High_spruce") and (ds.MIC_no[i] == 6) and (Thinn_HS_tag == True) and (fertilization == False)  and (ds.t[i] >= Thinn_age + 10):
            
                        #ds.MIC_no[i] = 6
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                            
                    elif (ds.mic_type[i] == "Low_spruce") and (ds.MIC_no[i] == 11) and (Thinn_LS_tag == False) and (fertilization == False): 
            
                        #ds.MIC_no[i] = 11
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                    elif (ds.mic_type[i] == "broadleaf")  and (ds.MIC_no[i] == 12) and (Thinn_BL_tag == False) and (fertilization == False):   

                         #ds.MIC_no[i] = 12
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 20
                        Establishment_age = ds.t[i] + 20
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100 
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                         
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
            
                    
                elif (ds.t[i] >= harvest_age_variable) and (__SI__ < 10.5 ) and (ds.MIC_no[i] in [1,4,5,6,7,8]) and (ds.mic_type[i] in MIC_L10_CC): 
                    
                    if (ds.mic_type[i] == "High_pine") and (ds.MIC_no[i] == 1) and (Thinn_HP_tag == False) and (fertilization == False):
            
                        #ds.MIC_no[i] = 1
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                         
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB, R_co2, R_biomass, R_carbon, R_carbon_stems, R_carbon_roots, R_co2_stems, R_co2_roots,
                                         R_G, Removed_trees, R_vol_tot, R_vol_spruce, R_vol_pine, R_vol_birch, R_vol_others, 
                                         R_vol_ros, R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")

                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                        
                    elif (ds.mic_type[i] == "Medium_spruce") and (ds.MIC_no[i] == 6) and (Thinn_MS_tag == False) and (fertilization == False):
            
                        #ds.MIC_no[i] = 6 
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                        
                    elif (ds.mic_type[i] == "High_spruce") and (ds.MIC_no[i] == 4) and (Thinn_HS_tag == False) and (fertilization == False):
            
                        #ds.MIC_no[i] = 4
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = True
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))  
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    # This scenario is identical to previeos one    
                    # elif (ds.mic_type[i] == "High_spruce") and (Thinn_HS_tag == False) and (fertilization == False):
                    #     ds.MIC_no[i] = 5  
                    #     this_period = ds.p[i]
                    #     Clear_cut_tag = True
                    #     Site_prep_after_harvesting = True
                    #     Next_Rotation_age =  ds.t[i] + harvest_age_variable 
                    #     ds.mgt[i] = self.mgt["clear cut"]                
                    #     self.prescription.add_clear_cut(period = this_period)
                    #     ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    #     Removed_trees = ds.Nr[i]
                    #     mic_tp = ds.mic_type[i]
                        
                    #     self.plot.fR_CC(Removed_trees, mic_tp ,**ds0)
                        
                    #     ds.Gr[i] = ds.Gb[i] - round(self.plot.fGp(i,**ds0),2)
                        
                    elif (ds.mic_type[i] == "Low_spruce") and (ds.MIC_no[i] == 7) and (Thinn_LS_tag == False) and (fertilization == False):
            
                        #ds.MIC_no[i] = 7
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 15
                        Establishment_age = ds.t[i] + 15
                        Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2 = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                        
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                        
                    
                    elif (ds.mic_type[i] == "broadleaf") and (ds.MIC_no[i] == 8) and (Thinn_BL_tag == False) and (fertilization == False):
                                                
                         #ds.MIC_no[i] = 8
                        this_period = ds.p[i]
                        Clear_cut_tag = True
                        Site_prep_after_harvesting = False
                        waiting_time = 25
                        Establishment_age = ds.t[i] + 25
                        Next_Rotation_age =  ds.t[i] + self.Harvest_age + waiting_time + 5
                        ds.mgt[i] = self.mgt["clear cut"]                
                        self.prescription.add_clear_cut(period = this_period)
                        ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                        G_left = ds.Gb[i] * 0.1
                        G_b = ds.Gb[i]
                        R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100 
                        R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                        R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                        R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                        
                        R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                        R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                        R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                        R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                        R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                        R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                        R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                         
                        Removed_trees = ds.Nr[i]
                        mic_tp = ds.mic_type[i]
                        
                        """ this line is to remove the trees required in clear-cut and update the objects """ 
                        self.plot.fR_CC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                         R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                         R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "clear cut")
                        
                        Product_tag_cc  = True
                        
                        
                        ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                        
                        ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                        ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                        ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                        ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                        ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                        ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                        ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                        
                        ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                        ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                        ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))     
                        ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                        ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] - self.plot.fCO(**ds0)[4]),'.2f'))
                        ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                        ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                        ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                
        return Clear_cut_tag, Site_prep_after_harvesting, Next_Rotation_age, ds.mgt[i], ds.Nr[i], ds.Gr[i], Establishment_age, Product_tag_cc, ds.Vr_tot[i], ds.Vr_spruce[i], ds.Vr_pine[i], ds.Vr_birch[i], ds.Vr_others[i], ds.Vr_ros[i], ds.Vr_warm[i], ds.R_BGB[i], ds.R_co2[i], ds.R_biomass[i], ds.R_carbon[i] , ds.R_carbon_stems[i],ds.R_carbon_roots[i],ds.R_co2_stems[i] , ds.R_co2_roots[i]
         

                                                # %%%%%%          Seed tree cut           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
    
    def seed_tree_cut_Implementation(self,i , ds_, ds0_,Thinn_MP_tag,Thinn_HP_tag, harvest_age_variable , Thinn_age, fertilization , Next_Rotation_age, seed_tree_cut_tag, Site_prep_after_harvesting, Establishment_age = 0):
        
        ds = ds_
        ds0 = ds0_
        
        dfGE_15 = self.prescription.management[self.prescription.management['Site index'] == "GE_15.5"]
        df10_15 = self.prescription.management[self.prescription.management['Site index'] == "10.5-15.5"]
        dfL_10 = self.prescription.management[self.prescription.management['Site index'] == "L_10.5"] 

        Product_tag_sc  = False
        if ds.t[i] >= Next_Rotation_age :
            
            dfGE_15_SC =  dfGE_15[dfGE_15["harvesting_method"] == "seed_tree_cut"]
            df10_15_SC =  df10_15[df10_15["harvesting_method"] == "seed_tree_cut"]
            dfL_10_SC  =  dfL_10 [dfL_10 ["harvesting_method"] == "seed_tree_cut"]  
            
            MIC_GE15_SC =[]
            for idx,row in dfGE_15_SC.iterrows():
                MIC_GE15_SC.append(row["MIC_type"])

            MIC_10_15_SC =[]
            for idx,row in df10_15_SC.iterrows():
                MIC_10_15_SC.append(row["MIC_type"]) 

            MIC_L10_SC =[]
            for idx,row in dfL_10_SC.iterrows():
                MIC_L10_SC.append(row["MIC_type"])            
            
            if (ds.t[i] >= harvest_age_variable) and (__SI__ >= 15.5) and (ds.MIC_no[i] in [2,3,4,5]) and (ds.mic_type[i] in MIC_GE15_SC):
                
                if (ds.mic_type[i] == "High_pine") and (ds.MIC_no[i] == 2) and (Thinn_HP_tag == False) and (fertilization == False):
                    #ds.MIC_no[i] = 2
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = True
                    waiting_time = 15
                    Establishment_age = ds.t[i] + 15
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period)
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] - self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                elif (ds.mic_type[i] == "High_pine") and (ds.MIC_no[i] == 3) and (Thinn_HP_tag == True) and (fertilization == False) and (ds.t[i] >= Thinn_age + 10):
                    #ds.MIC_no[i] = 3
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = True
                    waiting_time = 15
                    Establishment_age = ds.t[i] + 15
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period)
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    #print( (ds.Nr[i], ds.Nb[i] ))
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                elif (ds.mic_type[i] == "Medium_pine") and (ds.MIC_no[i] == 4) and (Thinn_MP_tag == False) and (fertilization == False):
                    #ds.MIC_no[i] = 4 
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = False
                    waiting_time = 15
                    Establishment_age = ds.t[i] + 15
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period)
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    #print( self.prescription.actions.TI[i+self.inc]/100)
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))  
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] - self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                elif (ds.mic_type[i] == "Medium_pine") and (ds.MIC_no[i] == 5) and (Thinn_MP_tag == True) and (fertilization == False) and (ds.t[i] >= Thinn_age + 10):
                    #ds.MIC_no[i] = 5 
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = False
                    waiting_time = 15
                    Establishment_age = ds.t[i] + 15
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period)
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    #print( self.prescription.actions.TI[i+self.inc]/100)
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                                        
            elif (ds.t[i] >= harvest_age_variable) and (__SI__ < 15.5) and (__SI__ >= 10.5 ) and (ds.MIC_no[i] in [2,3,4,5]) and (ds.mic_type[i] in MIC_10_15_SC): 

                
                if (ds.mic_type[i] == "High_pine") and (ds.MIC_no[i] == 2) and (Thinn_HP_tag == False) and (fertilization == False):
                    #ds.MIC_no[i] = 2
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = True
                    waiting_time = 20
                    Establishment_age = ds.t[i] + 20
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period)
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    #print( self.prescription.actions.TI[i+self.inc]/100)
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f'))  
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                elif (ds.mic_type[i] == "High_pine") and (ds.MIC_no[i] == 3) and (Thinn_HP_tag == True) and (fertilization == False) and (ds.t[i] >= Thinn_age + 10):
                    #ds.MIC_no[i] = 3
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = True
                    waiting_time = 20
                    Establishment_age = ds.t[i] + 20
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period) 
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]

                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f'))
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                elif (ds.mic_type[i] == "Medium_pine") and (ds.MIC_no[i] == 4) and (Thinn_MP_tag == False) and (fertilization == False):
                    #ds.MIC_no[i] = 4 
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = False
                    waiting_time = 20
                    Establishment_age = ds.t[i] + 20
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period)
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    #print( self.prescription.actions.TI[i+self.inc]/100)
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))  
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                elif (ds.mic_type[i] == "Medium_pine") and (ds.MIC_no[i] == 5) and (Thinn_MP_tag == True) and (fertilization == False) and (ds.t[i] >= Thinn_age + 10):
                    #ds.MIC_no[i] = 5 
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = False
                    waiting_time = 15
                    Establishment_age = ds.t[i] + 15
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period)
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    #print( self.prescription.actions.TI[i+self.inc]/100)
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))

                
            elif (ds.t[i] >= harvest_age_variable) and (__SI__ < 10.5 ) and (ds.MIC_no[i] in [2,3]) and (ds.mic_type[i] in dfL_10_SC): 
                
                if (ds.mic_type[i] == "High_pine") and (ds.MIC_no[i] == 2) and (Thinn_HP_tag == False) and (fertilization == False):
                    #ds.MIC_no[i] = 2
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = True
                    waiting_time = 25
                    Establishment_age = ds.t[i] + 25
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period)
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    #print( self.prescription.actions.TI[i+self.inc]/100)
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))   
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f'))
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                    
                elif (ds.mic_type[i] == "Medium_pine") and (ds.MIC_no[i] == 3) and (Thinn_MP_tag == False) and (fertilization == False):
                    #ds.MIC_no[i] = 3 
                    this_period = ds.p[i]
                    seed_tree_cut_tag = True
                    Site_prep_after_harvesting = False
                    waiting_time = 25
                    Establishment_age = ds.t[i] + 25
                    Next_Rotation_age =  ds.t[i] + harvest_age_variable + waiting_time + 5
                    ds.mgt[i] = self.mgt["seed tree cut"]                
                    self.prescription.add_seedtree_cut(period = this_period) 
                    ds.Nr[i] = ds.Nb[i] * self.prescription.actions.TI[i+self.inc]/100
                    G_left = ds.Gb[i] * 0.15
                    G_b = ds.Gb[i]
                    #print( self.prescription.actions.TI[i+self.inc]/100)
                    R_G          = ds.Gb[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_tot    =  ds.Vb[i] * self.prescription.actions.TI[i+self.inc]/100                
                    R_vol_spruce =  ds.Vb_spruce[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_pine   =  ds.Vb_pine[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_birch  =  ds.Vb_birch[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_others =  ds.Vb_others[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_ros    =  ds.Vb_ros[i] * self.prescription.actions.TI[i+self.inc]/100
                    R_vol_warm   =  ds.Vb_warm[i]* self.prescription.actions.TI[i+self.inc]/100 
                    
                    R_BGB           = ds.Initial_BGB_living[i]  * self.prescription.actions.TI[i+self.inc]/100         
                    R_co2           = ds.Initial_co2_living[i]  * self.prescription.actions.TI[i+self.inc]/100        
                    R_biomass       = ds.Initial_biomass_living[i] * self.prescription.actions.TI[i+self.inc]/100                 
                    R_carbon        = ds.Initial_carbon_living[i]  * self.prescription.actions.TI[i+self.inc]/100      
                    R_carbon_stems  = ds.Initial_carbon_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_carbon_roots  = ds.Initial_carbon_roots_living[i]  * self.prescription.actions.TI[i+self.inc]/100
                    R_co2_stems     = ds.Initial_co2_stems_living[i]  * self.prescription.actions.TI[i+self.inc]/100  
                    R_co2_roots     = ds.Initial_co2_roots_living[i] * self.prescription.actions.TI[i+self.inc]/100 
                    
                    Removed_trees = ds.Nr[i]
                    mic_tp = ds.mic_type[i]
                    
                    """ this line is to remove the trees required in seed-tree-cut and update the objects """ 
                    self.plot.fR_SC(R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots,
                                     R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                                     R_vol_warm, G_b, G_left, mic_tp,  ds.Year[i], ds.p[i], "seed tree cut")
                    
                    Product_tag_sc  = True
                    
                    ds.Gr[i] = float(format((ds.Gb[i] - self.plot.fGp(i,**ds0)),'.2f')) 
                    
                    ds.Vr_tot[i]    = float(format((ds.Vb[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[0]),'.2f'))  
                    ds.Vr_spruce[i] = float(format((ds.Vb_spruce[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[1]),'.2f'))
                    ds.Vr_pine[i]   = float(format((ds.Vb_pine[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[2]),'.2f'))
                    ds.Vr_birch[i]  = float(format((ds.Vb_birch[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[3]),'.2f'))
                    ds.Vr_others[i] = float(format((ds.Vb_others[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[4]),'.2f'))
                    ds.Vr_ros[i]    = float(format((ds.Vb_ros[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[5]),'.2f'))
                    ds.Vr_warm[i]   = float(format((ds.Vb_warm[i] - self.plot.fV(i,after=ds.Nr[i] > 0., **ds.loc[i])[6]),'.2f'))
                    
                    ds.R_BGB[i]          = float(format((ds.Initial_BGB_living[i] - self.plot.fCO(**ds0)[0]),'.2f'))
                    ds.R_co2[i]          = float(format((ds.Initial_co2_living[i] - self.plot.fCO(**ds0)[1]),'.2f')) 
                    ds.R_biomass[i]      = float(format((ds.Initial_biomass_living[i] - self.plot.fCO(**ds0)[2]),'.2f'))    
                    ds.R_carbon[i]       = float(format((ds.Initial_carbon_living[i] - self.plot.fCO(**ds0)[3]) ,'.2f')) 
                    ds.R_carbon_stems[i] = float(format((ds.Initial_carbon_stems_living[i] -self.plot.fCO(**ds0)[4]),'.2f'))
                    ds.R_carbon_roots[i] = float(format((ds.Initial_carbon_roots_living[i] - self.plot.fCO(**ds0)[5]),'.2f'))
                    ds.R_co2_stems[i]    = float(format((ds.Initial_co2_stems_living[i]  - self.plot.fCO(**ds0)[6]),'.2f'))
                    ds.R_co2_roots[i]    = float(format((ds.Initial_co2_roots_living[i] - self.plot.fCO(**ds0)[7]),'.2f'))
                
                
        return seed_tree_cut_tag, Site_prep_after_harvesting, Next_Rotation_age, ds.mgt[i], ds.Nr[i], ds.Gr[i] , Establishment_age, Product_tag_sc, ds.Vr_tot[i], ds.Vr_spruce[i], ds.Vr_pine[i], ds.Vr_birch[i], ds.Vr_others[i], ds.Vr_ros[i], ds.Vr_warm[i], ds.R_BGB[i], ds.R_co2[i], ds.R_biomass[i], ds.R_carbon[i] , ds.R_carbon_stems[i],ds.R_carbon_roots[i],ds.R_co2_stems[i] , ds.R_co2_roots[i]
     
                                                    # %%%%%%%          No management           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
   
    
    def No_management(self,i, ds_, ds0_, Clear_cut_tag, seed_tree_cut_tag,Thinn_MS_tag,Thinn_MP_tag,Thinn_HS_tag,Thinn_HP_tag,Thinn_LS_tag, fertilization, Site_prep_after_harvesting):
        
        ds = ds_
        ds0 = ds0_
                 
        
        if (__SI__ >= 15.5) and (ds.MIC_no[i] == 13) and Clear_cut_tag == False and seed_tree_cut_tag == False and  Thinn_MS_tag == False and Thinn_MP_tag == False and Thinn_HS_tag == False and Thinn_HP_tag == False and Thinn_LS_tag == False and fertilization == False and Site_prep_after_harvesting == False:
            
            #ds.MIC_no[i] = 13
            ds.mgt[i] = self.mgt["none"]
                            
            
        elif (__SI__ < 15.5) and (__SI__ >= 10.5)  and (ds.MIC_no[i] == 13) and Clear_cut_tag == False and seed_tree_cut_tag == False and  Thinn_MS_tag == False and Thinn_MP_tag == False and Thinn_HS_tag == False and Thinn_HP_tag == False and Thinn_LS_tag == False and fertilization == False and Site_prep_after_harvesting == False:

            #ds.MIC_no[i] = 13
            ds.mgt[i] = self.mgt["none"]
                             
            
        elif (__SI__ < 10.5)  and (ds.MIC_no[i] == 9) and Clear_cut_tag == False and seed_tree_cut_tag == False and  Thinn_MS_tag == False and Thinn_MP_tag == False and Thinn_HS_tag == False and Thinn_HP_tag == False and Thinn_LS_tag == False and fertilization == False and Site_prep_after_harvesting == False:

            #ds.MIC_no[i] = 9
            ds.mgt[i] = self.mgt["none"]

        return Clear_cut_tag,seed_tree_cut_tag, ds.mgt[i]

                                                # %%%%%%%    
    
    def Regeneration_implementation(self, i, ds, ds0, Clear_cut_tag, seed_tree_cut_tag):

        dfGE_15 = self.prescription.management[self.prescription.management['Site index'] == "GE_15.5"]
        df10_15 = self.prescription.management[self.prescription.management['Site index'] == "10.5-15.5"]
        dfL_10 = self.prescription.management[self.prescription.management['Site index'] == "L_10.5"] 
                    
        MIC_GE15_Regen =[]
        for idx,row in dfGE_15.iterrows():
            MIC_GE15_Regen.append(row["MIC_type"])

        MIC_10_15_Regen =[]
        for idx,row in df10_15.iterrows():
            MIC_10_15_Regen.append(row["MIC_type"]) 

        MIC_L10_Regen =[]
        for idx,row in dfL_10.iterrows():
            MIC_L10_Regen.append(row["MIC_type"])          
        
        if (__SI__ >= 15.5) and (ds.mic_type[i] in MIC_GE15_Regen):
            
            # the tags need to be False after regeneration
            if (ds.mic_type[i] == "High_pine") and Clear_cut_tag == True and seed_tree_cut_tag == False:

                Regen_species = "Pine"
                Regen_density =  2200
                self.plot.fRegen(Regen_species, Regen_density, ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
            elif (ds.mic_type[i] == "High_pine") and Clear_cut_tag == False and seed_tree_cut_tag == True:

                Regen_species = "Pine"
                Regen_density =  2200
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                seed_tree_cut_tag = False
            
            elif (ds.mic_type[i] == "Medium_pine") and Clear_cut_tag == False and seed_tree_cut_tag == True:
                # 1500 NR_under_seed_trees and 200 NR
                Regen_species = "Pine"
                Regen_density =  1500
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
                seed_tree_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
            
            elif (ds.mic_type[i] == "High_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                Regen_species = "Spruce"
                Regen_density =  3000
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
            elif (ds.mic_type[i] == "Medium_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                # 2500 Planting and 200 NR
                Regen_species = "Spruce"
                Regen_density =  2500
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
                
                               
            elif (ds.mic_type[i] == "Low_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                # 1800 Planting and 200 NR
                Regen_species = "Spruce"
                Regen_density =  1800
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
                
            elif (ds.mic_type[i] == "broadleaf") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                
                Regen_species = "Birch"
                Regen_density =  2000
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
                Clear_cut_tag = False
                
                Regen_species = "Spruce"
                Regen_density =  400
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])                
                
            else:
                Regen_species = "Birch"
                Regen_density =  500
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
                
                Regen_species = "Spruce"
                Regen_density =  500
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])                
            
            
        elif (__SI__ < 15.5) and (__SI__ >= 10.5) and (ds.mic_type[i] in MIC_10_15_Regen):

            # the tags need to be False after regeneration
            if (ds.mic_type[i] == "High_pine") and Clear_cut_tag == True and seed_tree_cut_tag == False:

                Regen_species = "Pine"
                Regen_density =  1800
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
            elif (ds.mic_type[i] == "High_pine") and Clear_cut_tag == False and seed_tree_cut_tag == True:

                Regen_species = "Pine"
                Regen_density =  1800
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                seed_tree_cut_tag = False
            
            elif (ds.mic_type[i] == "Medium_pine") and Clear_cut_tag == False and seed_tree_cut_tag == True:
                # 1500 NR_under_seed_trees and 200 NR
                Regen_species = "Pine"
                Regen_density =  1200
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])  
                seed_tree_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
            
            elif (ds.mic_type[i] == "High_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                Regen_species = "Spruce"
                Regen_density =  2000
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
            elif (ds.mic_type[i] == "Medium_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                # 2500 Planting and 200 NR
                Regen_species = "Spruce"
                Regen_density =  1500
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 

            elif (ds.mic_type[i] == "Low_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                # 1800 Planting and 200 NR
                Regen_species = "Spruce"
                Regen_density =  1200
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
                
            elif (ds.mic_type[i] == "broadleaf") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                
                Regen_species = "Birch"
                Regen_density =  1000
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
                Regen_species = "Spruce"
                Regen_density =  200
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])                 
            else:
                Regen_species = "Birch"
                Regen_density =  300
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
                
                Regen_species = "Spruce"
                Regen_density =  300
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])  

          
            
        elif (__SI__ < 10.5) and (ds.mic_type[i] in MIC_L10_Regen):

            # the tags need to be False after regeneration
            if (ds.mic_type[i] == "High_pine") and Clear_cut_tag == True and seed_tree_cut_tag == False:

                Regen_species = "Pine"
                Regen_density =  1800
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
            elif (ds.mic_type[i] == "High_pine") and Clear_cut_tag == False and seed_tree_cut_tag == True:

                Regen_species = "Pine"
                Regen_density =  1800
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                seed_tree_cut_tag = False
            
            elif (ds.mic_type[i] == "Medium_pine") and Clear_cut_tag == True and seed_tree_cut_tag == True:
                # 1500 NR_under_seed_trees and 200 NR
                Regen_species = "Pine"
                Regen_density =  1200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                seed_tree_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
            
            elif (ds.mic_type[i] == "High_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                Regen_species = "Spruce"
                Regen_density =  2000
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
            elif (ds.mic_type[i] == "Medium_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                # 2500 Planting and 200 NR
                Regen_species = "Spruce"
                Regen_density =  1500 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 

            elif (ds.mic_type[i] == "Low_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:
                # 1800 Planting and 200 NR
                Regen_species = "Spruce"
                Regen_density =  1200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
                Regen_species = "Birch"
                Regen_density =  200
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                
            elif (ds.mic_type[i] == "Low_spruce") and Clear_cut_tag == True and seed_tree_cut_tag == False:     
                
                Regen_species = "Birch"
                Regen_density =  1000 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])
                Clear_cut_tag = False
                
                Regen_species = "Spruce"
                Regen_density =  200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i])             
                
            else:
                Regen_species = "Birch"
                Regen_density =  200 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
                
                Regen_species = "Spruce"
                Regen_density =  100 
                self.plot.fRegen(Regen_species, Regen_density,  ds.Year[i], ds.p[i]) 
        
        
        return Clear_cut_tag, seed_tree_cut_tag

          













                      