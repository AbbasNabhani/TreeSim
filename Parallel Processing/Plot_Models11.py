# -*- coding: utf-8 -*-
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
"""
plot-level growth model 

"""
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
__author__ = "Abbas Nabhani && Hanne Kathrine Sjolie"                                                                                       ###
__created_on__ = "Sat Apr  4 18:22:00 2020"                                                                                                 ###
__email__ = "forsim@inn.no"                                                                                                                 ###
__status__ = "Development of distance-independent individual tree simulator"                                                                ###
__version__ = "v0.1.0"                                                                                                                      ###                                                                                                                                                                                                                              
output_type = "Growth & yield curve"                                                                                                        ###
### Last Edit: 07 May 2022                                                                                                                  ###
                                                # %%%% import modules for stand level %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

from heapq import nlargest
from operator import itemgetter
from math import log, sqrt, exp, pi, gamma
import numpy as np
import Tree_Models11 as gm

                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

class Species(gm.GrowthModel):
    
    GROWTH2 =list()
    def __init__(self, **kwargs):
        
        self.tref = 40     # reference age in H40 system 
        gm.GrowthModel.__init__(self,**kwargs)
        


                                                # %%%%%    fMgt    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    def fMgt(self, mgt, **ds0):
        
        pass
        
                                                # %%%%   fdominant height    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    def fH0(self, Increment = False, **kwargs):
        """ 
        
        Calculates dominant height for all species calculated according to eq.1 in Sharma et al.(2011, 2017) 
        Parameters:
            SI_m(H40): Site index of spruce (m)
                Note:The site quality of the H40-system is based upon the top height (the middle height of the hundred trees per hectare 
                with the largest diametre) of the trees at the age of 40 years at breast height (1.3 m above ground level)
            self.t1: initial age for the dominant height (years)
            t2: age at the second point in time (years) 
            DHT1: Initial dominant height at age t1
            DHT2: Projected dominant height at age t2
            
        Returns:
            Dominant hegith (m)
        """
        N = kwargs["Na"]

        spruce_species = (1,2,3)
        scots_pine_species =(10,11,12,20,21,29)
        birch_species=(30,31)
        other_broadleaves_species=(50,51,54,59)
        ROS_species= (32,52,53,56)
        warm_species = (40,41,42,43,44,48,49,55,57,58,65,70)
        
        trees = [k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0]
        
        tree = [(t.height/10,t.dbh, t.tree_sp) for t in self.DERIVED_TREES.values()]
        # dom is the thickest tree in the stand among all the target species
        dom = [x[2] for x in nlargest(1,tree,key=itemgetter(1))] # output is a code (eg. 10, 30)
        
        
        
        if dom in spruce_species:
            dominant_species = "spruce"     
        elif dom in scots_pine_species:
            dominant_species = "scots_pine"
        elif dom in birch_species:
            dominant_species = "birch"     
        elif dom in other_broadleaves_species:
            dominant_species = "other_broadleaves"
        elif dom in ROS_species:
            dominant_species = "ROS"
        else:
            dominant_species = "warm"
            
        ages = []
        # we take the mean of ages because the species in each group can have different ages    
        # the increment = "not true" is used for calculating the t2 in order to compute the dominant height
        if not Increment:
            for s in trees:
                if self.DERIVED_TREES[s].n_tree != 0:
                    ages.append(self.DERIVED_TREES[s].t_age + 5)
            t2= np.mean(ages)

        # the increment = "False" is used to apply different t2 for the function fPOT 
        else:
            t2 = kwargs["t2"]
            
        
        if dominant_species == "spruce": 
            b1,b2,b3= 18.9206,5175.18,1.1576 
    
            X0 = 0.5 * (self.H0 - 1.3 - b1 + sqrt((self.H0 - 1.3 - b1) ** 2 + 4 * b2 * (self.H0 - 1.3) * self.t_Dtree ** -b3))
            if N != 0:
                h = (b1 + X0) / (1 + (b2 / X0 * (t2 ** (-b3)))) + 1.3
            else:
                h =0
        elif dominant_species == "scots_pine":
            b1,b2,b3= 12.8361,3263.99,1.1758 
        
            X0 = 0.5 * (self.H0 - 1.3 - b1 + sqrt((self.H0 - 1.3 - b1) ** 2 + 4 * b2 * (self.H0 - 1.3) * self.t_Dtree ** -b3))
            if N != 0:
                h = (b1 + X0) / (1 + (b2 / X0 * (t2 ** (-b3)))) + 1.3 
            else:
                h=0.
            
        elif dominant_species == "birch":
            b1,b2,k = 394, 1.387, 7
            D = b1/(k ** b2)
            
            R = sqrt((self.H0 - 1.3 - D)** 2 + 4 * b1 * (self.H0 - 1.3) / (self.t_Dtree ** b2))
            if N != 0:
                h = (self.H0 - 1.3 + D + R ) / (2 + 4 * b1 * t2 ** (-1 * b2) / (self.H0 - 1.3 - D + R)) + 1.3
            else:
                h = 0.0
        
        else:
            
            b1,b2,k = 394, 1.387, 7
            D = b1/(k ** b2)                                           #
            R = ((self.H0 - 1.3 - D)** 2 + 4 * b1 * (self.H0 - 1.3) / (self.t_Dtree ** b2))** 0.5
            if N != 0:
                h = (self.H0 - 1.3 + D + R ) / (2 + 4 * b1 * t2 ** (-1 * b2) / (self.H0 - 1.3 - D + R)) + 1.3
            else:
                h = 0.
            
#       self.GROWTH2.append((self.t1, t2, h))
        return  h
    
                                                # %%%% 
                                                
    def fPOT(self,**kwargs):
        """Calculating potential height increment
        DHT1 = self.fH0(t2 = self.t_Dtree) : Initial dominant height at age t1
        DHT2 = self.fH0(t2 = self.t_Dtree + 5 yrs): Projected dominant height at age t2
        """
        trees = [k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0]
        ages_0, ages_1 = [],[]
        for s in trees:
            ages_0.append(self.DERIVED_TREES[s].t_age)
            ages_1.append(self.DERIVED_TREES[s].t_age + 5)
        t2_0= np.mean(ages_0)
        t2_1= np.mean(ages_1)
        
        DHT1= self.fH0(Increment=True, t2 = t2_0)
        DHT2= self.fH0(Increment=True, t2 = t2_1)
        
        POT = DHT2 - DHT1
        return POT
    
                                                # %%%%     fNumber of trees    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 


    def fN(self, **kwargs):
        """
        t1: Actual age (years)
        t2: Age to the future (years)
        """
        N1 = kwargs["Na"]
        mortality = kwargs["mortality"]

        if mortality:
            return self.TPH()
        else:
            return N1       

                                                # %%%%     fBasal_area    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        
    def fGi(self, **kwargs):

        """
        Calculate initial basal area for each stand per hectare (observations)
        Return: stand basal area (m2ha-1)
        """
#
        #trees = [k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0]
        BAL = sum([(self.DERIVED_TREES[k].ba *self.DERIVED_TREES[k].n_tree) for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0])
        
        return BAL


    def fGp(self, i, **kwargs):
        """
        Calculate projected basal area 
        Return: stand basal area (m2ha-1)
        """       

        BAL = sum([(self.DERIVED_TREES[k].ba * self.DERIVED_TREES[k].n_tree) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)]) # if self.DERIVED_TREES[k].Period == i
            
        return BAL
    
    
                                                # %%%%    fVolume    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 


    def fV(self, i, after=False, **kwargs):
        """
        Calculate Total volume inside Bark of each plot [m³/ha]
        Divide by 1000 to get the units right
        Parameters
        ----------
        after : TYPE, optional
            DESCRIPTION. The default is False.
        **kwargs : TYPE
            DESCRIPTION.

        Returns
        -------
        volsum : TYPE
            Total volume inside Bark of each plot [m³/ha]

        """

        trees = [k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0]        
        if after:
            
            volsum = sum([(self.DERIVED_TREES[k].volsum + self.DERIVED_TREES[k].vol_increment) for k in trees])
            vol_spruce = sum([(self.DERIVED_TREES[k].vol_spruce + self.DERIVED_TREES[k].vol_increment) for k in trees]) 
            vol_pine = sum([(self.DERIVED_TREES[k].vol_pine + self.DERIVED_TREES[k].vol_increment) for k in trees]) 
            vol_birch = sum([(self.DERIVED_TREES[k].vol_birch + self.DERIVED_TREES[k].vol_increment) for k in trees])
            vol_others = sum([(self.DERIVED_TREES[k].vol_others + self.DERIVED_TREES[k].vol_increment) for k in trees])
            vol_ROS = sum([(self.DERIVED_TREES[k].vol_ROS + self.DERIVED_TREES[k].vol_increment) for k in trees])
            vol_warm =  sum([(self.DERIVED_TREES[k].vol_warm + self.DERIVED_TREES[k].vol_increment) for k in trees])
        
                    
        else:
    
            volsum = sum([(self.DERIVED_TREES[k].volsum + self.DERIVED_TREES[k].vol_increment) for k in trees]) 
            vol_spruce = sum([(self.DERIVED_TREES[k].vol_spruce + self.DERIVED_TREES[k].vol_increment) for k in trees])
            vol_pine = sum([(self.DERIVED_TREES[k].vol_pine + self.DERIVED_TREES[k].vol_increment) for k in trees]) 
            vol_birch = sum([(self.DERIVED_TREES[k].vol_birch + self.DERIVED_TREES[k].vol_increment) for k in trees]) 
            vol_others = sum([(self.DERIVED_TREES[k].vol_others + self.DERIVED_TREES[k].vol_increment) for k in trees]) 
            vol_ROS = sum([(self.DERIVED_TREES[k].vol_ROS + self.DERIVED_TREES[k].vol_increment) for k in trees]) 
            vol_warm =  sum([(self.DERIVED_TREES[k].vol_warm + self.DERIVED_TREES[k].vol_increment) for k in trees]) 
        
        return volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm


                                                # %%%%     f Carbon & CO2    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

    def fCO(self, **kwargs):
        """
        Calculate Total biomass(Ton/ha-1)/equivalent carbon/equivalent co2 of each plot
        Divide by 1000 to get the units right
        """ 
        
        trees = [k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0]
    
        BGB = sum([(self.DERIVED_TREES[k].BGB/1000  * self.DERIVED_TREES[k].n_tree) for k in trees])
        Tot_co2 = sum([(self.DERIVED_TREES[k].Tot_co2/1000  * self.DERIVED_TREES[k].n_tree) for k in trees])
        Tot_biomass = sum([(self.DERIVED_TREES[k].Tot_biomass/1000  * self.DERIVED_TREES[k].n_tree) for k in trees])
        Total_carbon = sum([(self.DERIVED_TREES[k].Total_carbon/1000  * self.DERIVED_TREES[k].n_tree) for k in trees])
        carbon_stems = sum([(self.DERIVED_TREES[k].Tot_carbon_stems/1000  * self.DERIVED_TREES[k].n_tree) for k in trees])
        carbon_roots = sum([(self.DERIVED_TREES[k].Tot_carbon_roots/1000  * self.DERIVED_TREES[k].n_tree) for k in trees])
        co2_stems =  sum([(self.DERIVED_TREES[k].Tot_co2_stems/1000  * self.DERIVED_TREES[k].n_tree) for k in trees])
        co2_roots = sum([(self.DERIVED_TREES[k].Tot_co2_roots/1000  * self.DERIVED_TREES[k].n_tree) for k in trees])

        
        return BGB, Tot_co2, Tot_biomass, Total_carbon, carbon_stems, carbon_roots, co2_stems, co2_roots

                                                # %%%%     fProducts    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
    
    def fProducts(self, i, **kwargs):
        
        """
        Product                   Specifications
        ------------------------------------------
        Sawtimber                    >=30.5 cm dbh
        Pulpwood                     >=15.1 cm dbh
        ------------------------------------------
        DBH (diameter breast height) is in mm, while H (Height) is in dm. 
        """
        
        products    = [k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0]            
        
        R_SSaw   =  sum([self.DERIVED_TREES[k].R_SSaw for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].Period == i]) 
        R_SPulp  =  sum([self.DERIVED_TREES[k].R_SPulp for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].Period == i])
        R_PSaw   =  sum([self.DERIVED_TREES[k].R_PSaw for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].Period == i])
        R_PPulp  =  sum([self.DERIVED_TREES[k].R_PPulp for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].Period == i])
        R_HSaw   =  sum([self.DERIVED_TREES[k].R_HSaw for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].Period == i])
        R_HPulp  =  sum([self.DERIVED_TREES[k].R_HPulp for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].Period == i])
        
        return R_SSaw, R_SPulp, R_PSaw, R_PPulp, R_HSaw, R_HPulp 

     
                                                # %%%%    End          %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
