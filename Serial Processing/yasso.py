# -*- coding: utf-8 -*-

"""
Created on Mon Nov 06 14:15:41 2021

@author: Nabhani
"""


"""
Created on Sat Mar 16 21:05:21 2019

@author: slauniai
"""

"""
Created on Mon Dec 10 17:56:56 2018

@author: lauren

results = YassoModel.decomp_one_timestep(0.251, 0.0758, 0.0866, 3.3)
print(results)

"""

import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
import xlrd

class yasso():
    def __init__(self):
        
        #ABBREVIATIONS:
        #    - nwl: non woody litter
        #    - fwl: fine woody litter
        #    - cwl: coarse woody litter
        #    - cel: cellulose
        #    - lig: lignin
        #    - hum: humus
        #    - ext: extractives
        
        #Initial values based on humus layer density
        rho = 120.  #density of humus layer kg/m3
        depth = 0.15 #m
        Cc = 0.5  #kg C/ kgOM
        self.xfwl = 0.05*depth*rho*Cc
        self.xcwl =0.05*depth*rho*Cc 
        self.xext =0.1*depth*rho*Cc
        self.xcel =0.1*depth*rho*Cc
        self.xlig =0.2*depth*rho*Cc
        self.xhum1 =0.2*depth*rho*Cc
        self.xhum2 = 0.3*depth*rho*Cc
    


    def map_carbon_to_NPK(self, CO2):
        """
        Relate amount of produced carbon to N, P and K amounts.
        CO2 --> C : x 12/44
        C --> CO2 : x 44/12 = 3.67
        Soil carbon (C) kg/m2
        nitrogen (N)
        phosphorus (P) 
        potassium (K)
        Organic matter (OM)
        """
        OM=CO2*12./44.*2.   #To released organic matter   C/CO2= ratio of 12/44 (the ratio of the molecular weight of carbon to carbon dioxide)
        # One ton of carbon equals 44/12 = 11/3 = 3.67 tons of carbon dioxide.
        #N = 0.015 * OM   #
        #P = 0.005 * OM
        #K = 0.008 * OM
        N = 0.01 * OM   #
        P = 0.001 * OM
        K = 0.005 * OM
        
        return N, P, K

    def decomp_one_timestep(self, unwl, ufwl, ucwl, temp):
        """
        Compute amount of CO2, N, P, K. Single yearly timestep.
        INPUT:
            - unwl, ufwl, ucwl: float. kg/m2 of non-woody, fine and coarse woody litter produced in that year.
            - temp: float, mean T, sum of T or log sum of T. With any of those changes, modify T0.
        """    
        # 50% OF MASS OF C IN LITTER 
        unwl = unwl * .5; ufwl = ufwl * .5; ucwl = ucwl * .5
        
        # Read parameters from given file
        param = decom_para()
                
        # Other parameters
        BETA = 0.106 # from paper
        T0 = -1.0
        SHUM = 0.6
        
        ### Concentration of carbon in each type of litter. Assumption: half of the litter is carbon.
        cnwl_ext, cfwl_ext, cnwl_cel, cnwl_ext, cnwl_lig, cfwl_cel, ccwl_cel, ccwl_ext, cfwl_lig, ccwl_lig = [0.5,0.5,0.5,0.5,0.5,0.5,0.5,0.5,0.5,0.5]
                        
        dt = 1. # year
        
        # variation of k and a with T
        kext = param['kext']*(1.0 + BETA * (temp - T0))
        klig = param['klig']*(1.0 + BETA * (temp - T0))
        kcel = param['kcel']*(1.0 + BETA * (temp - T0))
        khum1 = param['khum1']*(1.0 + SHUM * BETA * (temp - T0))
        khum2 = param['khum1']*(1.0 + SHUM * BETA * (temp - T0))
        acwl = param['acwl']*(1.0 + 0.4 * BETA * (temp - T0))
        afwl = param['afwl']*(1.0 + 0.4 * BETA * (temp - T0))
    
        CO2 = ((1.-param['pext'])*kext * self.xext + (1.-param['pcel'])*kcel * self.xcel +
               (1.-param['plig'])*klig * self.xlig + (1.-param['phum1'])*khum1 * self.xhum1 +
               1.0*khum2 * self.xhum2)
        
        CO = CO2 * 12./44
        
        # UPDATE VALLUE IN OBJECT LIKE SO: self.xfwl = xfwl1 
        # eqs (1-7)
        xfwl0 = self.xfwl
        xcwl0 = self.xcwl
        xext0 = self.xext
        xcel0 = self.xcel
        xlig0 = self.xlig
        xhum10 = self.xhum1
        xhum20 = self.xhum2
        
        self.xfwl = ufwl*dt + xfwl0*(1. - afwl*dt)
        self.xcwl = ucwl*dt + xcwl0*(1. - acwl*dt)
        self.xext = ((unwl*cnwl_ext + cfwl_ext*afwl*xfwl0 + ccwl_ext*acwl*xcwl0) * dt
                + xext0 * (1.0 - kext*dt))
        self.xcel = ((unwl*cnwl_cel + cfwl_cel*afwl*xfwl0 + ccwl_cel*acwl*xcwl0) * dt 
                + xcel0 * (1.0 - kcel*dt))
        self.xlig = ((unwl*cnwl_lig + cfwl_lig*afwl*xfwl0 + ccwl_lig*acwl*xcwl0 + param['pext']*kext*xext0 + param['pcel']*kcel*xcel0) * dt 
                + xlig0 * (1.0 - klig*dt))
        self.xhum1 = (param['plig']*klig*xlig0) * dt + xhum10 * (1.0 - khum1*dt)
        self.xhum2 = (param['phum1']*khum1*xlig0) * dt + xhum20 * (1.0 - khum2*dt)
               
        N, P, K = self.map_carbon_to_NPK(CO2)
        
        return CO2, CO, N, P, K
    

def decom_para():
    #Liski et al. 2005, Yasso-model
    ypara={
           'afwl':0.54,
           'acwl':0.05,
           'kext':0.6,
           'kcel':0.3,
           'klig':0.22,
           'khum1':0.012,
           'khum2':0.0012,
           'pext':0.2,
           'pcel':0.2,
           'plig':0.2,
           'phum1':0.2,
           }
    return ypara

#YassoModel = yasso()


