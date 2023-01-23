
# -*- coding: utf-8 -*-
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
"""
tree-level growth model 

"""
###############################################################################################################################################
__author__ = "Abbas Nabhani && Hanne Kathrine Sjolie"                                                                                       ###
__created_on__ = "Sat Apr  4 18:22:00 2020"                                                                                                 ###
__email__ = "forsim@inn.no"                                                                                                                 ###
__status__ = "Development of distance-independent individual tree simulator"                                                                ### 
__version__ = "v0.1.0"                                                                                                                      ###                                                                                                                                                                                                                             
output_type = "Growth & yield curve"                                                                                                        ###
### Last Edit: 07 May 2022                                                                                                                  ###
###############################################################################################################################################
###############################################################################################################################################
ingrowth_model = "Bollandsas"                                                                                                               ###
""" one can switch to other Diameter growth model (matrix model)"""                                                                         ###
#DiameterGrowth_model = "Weibull model"                                                                                                     ### 
DiameterGrowth_model = "matrix model"                                                                                                       ###
"""the grid size used for visualization purpose"""                                                                                          ###
_gridsize_x = 20                                                                                                                            ###
_gridsize_y = 20                                                                                                                            ###
"""The number of 5-year intervals """                                                                                                       ###
step = 40                                                                                                                                   ###
###############################################################################################################################################

                                                # %%%% import modules for individual tree   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%##
import titles_tree
#from simulation import Data, tree, plot
from math import log, sqrt, pi,exp, gamma, ceil
import numpy as np
from heapq import nlargest
from operator import itemgetter
from matplotlib import pyplot as plt
from simulation import Data, tree, Simulator
import collections
from collections import OrderedDict, defaultdict
import operator
#from labellines import labelLine, labelLines
import matplotlib.gridspec as gridspec
import statistics
from django.utils.crypto import get_random_string
import random
import yasso
import requests
import pandas as pd
#import pdb

YassoModel = yasso.yasso()

#******************************* for x and y of tree location
np.random.seed(1)
#np.set_printoptions(precision=2)
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
class GrowthModel():
    """ Represents individual trees.
    """
    
    Instances = {}
    Tree_dbh=collections.defaultdict(dict)
    Tree_volume=collections.defaultdict(dict)
    Tree_height=collections.defaultdict(dict)
    DERIVED_TREES = {}
    DeadTrees = collections.defaultdict(lambda:defaultdict(int))
    GROWTH=list()
    DiameterClass=list()
    Treeheight=list()
    volume= list()
    weatherDict= dict()      #this dict is filled with municipality id data
    weatherErrorDict= dict() #this dict is filled with county id data
    TITLES = collections.defaultdict(lambda:defaultdict(int))
    Periods_dict = defaultdict(list)
    new_cls_name_list = list()
  
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  
    @classmethod
    def TreeGenerator(cls, new_cls_name, new_parameters):
        """ Creates a Tree subclass to represent a Functional Type.

            Args:
                new_cls_name: str
                    Name of the functional type

                new_parameters: dict
                    Dictionary containing the the parameters specific to each functional type.
                    The following format is expected:
                        {   'plot_id':value,
                            'tree_id':value,
                            'tree_sp':value,
                            'dbh':value,
                            'height':value,
                            'diameter_class':value,
                            'tree_Factor':value,
                            'SI_spp':value,
                            'SI_m':value, 
                            'LAT':value,
                            't_age':value,
                        }

                Returns: Tree subclass
                    A subclass of the Tree class with the provided parameter values as default.
        """

        def new_init(self, **kwargs):

            super().__init__()

            self.plot_id = new_parameters['plot_id']
            self.tree_id = new_parameters['tree_id']
            self.tree_sp = new_parameters['tree_sp']
            self.dbh = new_parameters['dbh']
            self.height = new_parameters['height']
            self.diameter_class = new_parameters['diameter_class']
            self.tree_Factor = new_parameters['tree_Factor']
            self.n_tree = new_parameters['n_tree']
            self.SI_spp = new_parameters['SI_spp']
            self.altitude_m  = new_parameters['altitude_m']
            self.SI_m = new_parameters['SI_m']
            self.LAT = new_parameters['LAT']
            self.species = new_parameters['species']
            self.t_age = new_parameters['t_age']
            self.year = new_parameters['year']
            self.Num_DeadTrees = new_parameters['Num_DeadTrees']
            self.Dom_species = new_parameters['Dom_species']
            self.Total_carbon = new_parameters['Total_carbon']
            self.Tot_biomass = new_parameters['Tot_biomass']
            self.Tot_co2 = new_parameters['Tot_co2']
            self.BGB = new_parameters['BGB']
            self.vol_increment = new_parameters['vol_increment']
            self.dead_volume   = new_parameters['dead_volume']
            self.dead_BGB      = new_parameters['dead_BGB']
            self.dead_co2      = new_parameters['dead_co2']   
            self.dead_biomass  = new_parameters['dead_biomass']
            self.stationID     = new_parameters['stationID']
            self.coord_x = new_parameters['coord_x']
            self.coord_y = new_parameters['coord_y']
            self.Ftype         = new_cls_name
            self.DBH =0
            self.t_Dtree =0
            self.t2= 0
            self.Period=0           
            self.volsum = new_parameters['volsum']
            self.vol_spruce = new_parameters['vol_spruce']
            self.vol_pine = new_parameters['vol_pine']
            self.vol_birch = new_parameters['vol_birch']
            self.vol_others = new_parameters['vol_others']
            self.vol_ROS = new_parameters['vol_ROS']
            self.vol_warm = new_parameters['vol_warm'] 
            self.ba = new_parameters['ba']
            self.management = new_parameters['management']
                
        new_attr_met = {'DeadList':{'yr_since_dead': new_parameters['yr_since_dead'], 'Num_DeadTrees': new_parameters['Num_DeadTrees'],'dead_volume': new_parameters['dead_volume'],
                                    'dead_co2': new_parameters['dead_co2'], 'dead_biomass': new_parameters['dead_biomass'],
                                    'dead_C': new_parameters['dead_C'], 'dbh': new_parameters['dbh']},
                        'plot_id'        : new_parameters['plot_id'],
                        'tree_id'        : new_parameters['tree_id'],
                        'tree_sp'        : new_parameters['tree_sp'],
                        'dbh'            : new_parameters['dbh'],
                        'height'         : new_parameters['height'],
                        'diameter_class' : new_parameters['diameter_class'],
                        'tree_Factor'    : new_parameters['tree_Factor'],
                        'n_tree'         : new_parameters['n_tree'],
                        'SI_spp'         : new_parameters['SI_spp'],
                        'altitude_m'     : new_parameters['altitude_m'],
                        'SI_m'           : new_parameters['SI_m'],
                        'LAT'            : new_parameters['LAT'],
                        'species'        : new_parameters['species'],
                        't_age'          : new_parameters['t_age'],
                        'year'           : new_parameters['year'],
                        'Period'         : new_parameters['Period'], 
                        'yr_since_dead'  : new_parameters['yr_since_dead'], 
                        'Num_DeadTrees'  : new_parameters['Num_DeadTrees'],
                        'Dom_species'    : new_parameters['Dom_species'],   
                        'BGB'            : new_parameters['BGB'],
                        'Tot_co2'        : new_parameters['Tot_co2'],
                        'Tot_biomass'    : new_parameters['Tot_biomass'],
                        'Total_carbon'   : new_parameters['Total_carbon'], 
                    'Tot_carbon_stems'   : new_parameters['Tot_carbon_stems'],
                    'Tot_carbon_roots'   : new_parameters['Tot_carbon_roots'],
                       'Tot_co2_stems'   : new_parameters['Tot_co2_stems'],
                       'Tot_co2_roots'   : new_parameters['Tot_co2_roots'],
                        'vol_increment'  : new_parameters['vol_increment'],
                        'dead_volume'    : new_parameters['dead_volume'],                             
                        'dead_co2'       : new_parameters['dead_co2'],
                        'dead_biomass'   : new_parameters['dead_biomass'],
                        'dead_C'         : new_parameters['dead_C'],
                        'R_SPulp'        : new_parameters['R_SPulp'],
                        'R_PPulp'        : new_parameters['R_PPulp'],
                        'R_HPulp'        : new_parameters['R_HPulp'],
                        'R_SSaw'         : new_parameters['R_SSaw'],
                        'R_PSaw'         : new_parameters['R_PSaw'],
                        'R_HSaw'         : new_parameters['R_HSaw'],
                        'Biomass_BAR'    : new_parameters['Biomass_BAR'],
                        'Biomass_LGR'    : new_parameters['Biomass_LGR'],
                        'Biomass_RGE5'   : new_parameters['Biomass_RGE5'],
                        'Biomass_RLT5'   : new_parameters['Biomass_RLT5'],   
                        'unwl'           : new_parameters['unwl'],
                        'ufwl'           : new_parameters['ufwl'],
                        'ucwl'           : new_parameters['ucwl'],
                        'temp'           : new_parameters['temp'],
                        'coord_x'        : new_parameters['coord_x'],
                        'coord_y'        : new_parameters['coord_y'],
                        'volsum'         : new_parameters['volsum'],
                        'vol_spruce'     : new_parameters['vol_spruce'],
                        'vol_pine'       : new_parameters['vol_pine'],
                        'vol_birch'      : new_parameters['vol_birch'],
                        'vol_others'     : new_parameters['vol_others'],
                        'vol_ROS'        : new_parameters['vol_ROS'],
                        'vol_warm'       : new_parameters['vol_warm'],
                        'ba'             : new_parameters['ba'],
                        'management'     : new_parameters['management'],
                        'Ftype'          : new_cls_name,
                        '__init__'       : new_init}
        
        
        new_cls = type(new_cls_name, (cls,), new_attr_met)
            
            # if cls.DERIVED_TREES[new_cls_name].DeadList['Period'] 
            #GrowthModel.GROWTH.append((cls.DERIVED_TREES[new_cls_name].DeadList['dead_biomass']))
             
#        GrowthModel.Periods_dict[new_attr_met['Ftype']].append(new_attr_met['Period'])
            
        cls.DERIVED_TREES[new_cls_name] = new_cls
        
        """Record the Dead trees in the DeadTrees dict"""
        cls.DeadTrees[new_cls_name][cls.DERIVED_TREES[new_cls_name].Period] = new_attr_met['Num_DeadTrees']
        
#        GrowthModel.GROWTH.append((cls.DeadTrees))
        #       base.GrowthModel.DeadTrees['110191'][1][0]
        GrowthModel.TITLES[new_cls_name][new_attr_met['Period']] = (titles_tree.TreeObject(cls.DERIVED_TREES[new_cls_name].plot_id, cls.DERIVED_TREES[new_cls_name].tree_id, cls.DERIVED_TREES[new_cls_name].tree_sp, cls.DERIVED_TREES[new_cls_name].dbh, 
                                          cls.DERIVED_TREES[new_cls_name].height, cls.DERIVED_TREES[new_cls_name].diameter_class, cls.DERIVED_TREES[new_cls_name].tree_Factor, cls.DERIVED_TREES[new_cls_name].SI_spp,
                                          cls.DERIVED_TREES[new_cls_name].SI_m, cls.DERIVED_TREES[new_cls_name].n_tree, cls.DERIVED_TREES[new_cls_name].species, cls.DERIVED_TREES[new_cls_name].Period,
                                          cls.DERIVED_TREES[new_cls_name].coord_x, cls.DERIVED_TREES[new_cls_name].coord_y, cls.DERIVED_TREES[new_cls_name].year, cls.DERIVED_TREES[new_cls_name].volsum,
                                          cls.DERIVED_TREES[new_cls_name].vol_spruce,cls.DERIVED_TREES[new_cls_name].vol_pine,cls.DERIVED_TREES[new_cls_name].vol_birch,cls.DERIVED_TREES[new_cls_name].vol_others,
                                          cls.DERIVED_TREES[new_cls_name].vol_ROS,cls.DERIVED_TREES[new_cls_name].vol_warm, cls.DERIVED_TREES[new_cls_name].management))

        
        return new_cls

    @classmethod
    def UpdateTrees(cls, mortality, year, period):
        """Updates all living trees

            Returns: None
        """

        trees = [k for k in cls.DERIVED_TREES.keys()] #if cls.DERIVED_TREES[k].n_tree != 0
        
        for t in trees:
            treeObj = cls.DERIVED_TREES[t]
            cls.update(treeObj,t, mortality)
#            GrowthModel.GROWTH.append((t,cls.DERIVED_TREES[t].Period))
        if ingrowth_model == 'Bollandsas':
            ingrowthN = cls.inGrowthModel_Bollandsas(cls.DERIVED_TREES)
        if  (ingrowthN < 5) and (ingrowthN > 0):
            ingrow_trees = 1
        elif (ingrowthN < 10):
            ingrow_trees = 2
        else:
            ingrow_trees = 3
            
        if ingrowthN >= 1:
            Plot_trees = len([k for k in cls.DERIVED_TREES.keys()])
            tree_ids = []
            stop = 0
            ingrowth_parameters = cls.ingrowth_species(cls.DERIVED_TREES)

####********************************************            
            s1 = ingrowth_parameters[0][3]
            prop1 = ingrowth_parameters[0][2]
            a1= ingrowth_parameters[0][4]
            b1= ingrowth_parameters[0][5]
####********************************************
            s2 = ingrowth_parameters[1][3]
            prop2 = ingrowth_parameters[1][2]
            a2= ingrowth_parameters[1][4]
            b2= ingrowth_parameters[1][5]   
####********************************************
            s3 = ingrowth_parameters[2][3]
            prop3 = ingrowth_parameters[2][2]
            a3= ingrowth_parameters[2][4]
            b3= ingrowth_parameters[2][5]              
####********************************************
            s4 = ingrowth_parameters[3][3]
            prop4 = ingrowth_parameters[3][2]
            a4= ingrowth_parameters[3][4]
            b4= ingrowth_parameters[3][5] 
####********************************************
            s5 = ingrowth_parameters[4][3]
            prop5 = ingrowth_parameters[4][2]
            a5= ingrowth_parameters[4][4]
            b5= ingrowth_parameters[4][5] 
####********************************************
            s6 = ingrowth_parameters[5][3]
            prop6 = ingrowth_parameters[5][2]
            a6= ingrowth_parameters[5][4]
            b6= ingrowth_parameters[5][5] 

            
            while stop < ingrow_trees:
                id_= cls.tree_id_generation(cls.DERIVED_TREES[s1],s1)
                if id_ not in cls.DERIVED_TREES.keys():
                    tree_ids.append( id_) 
                    stop += 1                          
                    if len(tree_ids) >= ingrow_trees:
                        break

            j = 0
            for i in range((Plot_trees + 1) , (Plot_trees + ingrow_trees+ 1)):
                j += 1
                tree_id        = tree_ids[i - (Plot_trees + 1)]
                if j==1:
                    s = s1
                    a = a1
                    b = b1
                elif j==2:
                    if prop2 >= 0.4:
                        s = s2
                        a = a2
                        b = b2
                    else:                        
                        s = s1
                        a = a1
                        b = b1
                elif j == 3:
                    if (prop2 < 0.4) and (prop2 >= 0.2):
                        s = s2
                        a = a2
                        b = b2
                    else:
                        s = s1
                        a = a1
                        b = b1    
                                              
                cls.ingrowth_implementation(cls.DERIVED_TREES,ingrowthN, ingrow_trees, tree_id, i, s, year, period)
            


    @classmethod        
    def TPH(self):
        """Calculate the plot total number of trees per hectare (ha-1)

        Returns: float
            Number of trees per hectare.
        """ 
        N = sum([self.DERIVED_TREES[k].n_tree for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0])

        return N
    
    @classmethod
    def TPP(self):
        
        """Calculate the plot total number of trees 

        Returns: float
            Number of trees in plot.
        """ 
        n_tree = len([k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0])
        
        return n_tree
   
    @classmethod
    def DTP(self):
        
        """Calculate the plot total number of dead trees 

        Returns: float
            Number of dead trees in plot.
        """ 
        n_dead = len([k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree == 0])
        
        return n_dead
        
        
    @classmethod        
    def Dominant_Height(self):
        """ Finds the mean height of the two thickest trees in each plot (Mean quadratic diameter of 100 thickest trees/ha of one species [cm]). 

        Returns:
            (float): height of the two thickest trees.

        """ 
        # trees = [k for k in self.DERIVED_TREES.keys()]
        # for t in trees:
        trees = [(t.height/10,t.dbh, t.tree_sp) for t in GrowthModel.DERIVED_TREES.values()]
        # dom is the thickest tree in the plot among all the target species
        dom = [x[2] for x in nlargest(1,trees,key=itemgetter(1))] # output is a code (eg. 10, 30)
        # height_largest_dbh is the two tickest trees in the plot
        
        height_largest_dbh = [x[0] for x in nlargest(2,trees,key=itemgetter(1)) if [x[2]] == dom]

        Ddom = np.mean(height_largest_dbh)
        return Ddom, dom
    
                   
                                                # %%%%%  Initialization %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%55
    def __init__(self,**kwargs):
        
        super().__init__()
        
        self.year= kwargs["year"]
        self.t = kwargs["t"]
        self.LATITUDE= kwargs["Latitude"]
        self.Altitude= kwargs["Altitude"]
        self.subplot_size = kwargs["subplot_size"]
        self.Region= kwargs["Region"]
        self.trObject= kwargs["Data"]
        self.plot_id = str(kwargs["plot_id"])
        self.tref = 40       # reference age in H40 system
        self.treeList= list(kwargs["treeList"])
 
        for k in self.treeList:

            self_template = GrowthModel.TreeGenerator(new_cls_name = str(k), new_parameters= dict(plot_id  = self.trObject.trees[k].plot_id,
                                                                                            tree_id        = self.trObject.trees[k].tree_id,
                                                                                            tree_sp        = self.trObject.trees[k].tree_sp,
                                                                                            dbh            = self.trObject.trees[k].dbh,
                                                                                            height         = self.trObject.trees[k].height,
                                                                                            diameter_class = self.trObject.trees[k].diameter_class,
                                                                                            tree_Factor    = self.trObject.trees[k].tree_Factor,
                                                                                            n_tree         = self.trObject.trees[k].n_tree,
                                                                                            SI_spp         = self.trObject.trees[k].SI_spp,
                                                                                            altitude_m     = self.trObject.trees[k].altitude_m,
                                                                                            SI_m           = self.trObject.trees[k].SI_m,
                                                                                            LAT            = self.trObject.trees[k].LAT,
                                                                                            species        = self.trObject.trees[k].species,
                                                                                            t_age          = self.trObject.trees[k].t_age,
                                                                                            year           = self.trObject.trees[k].year,
                                                                                            Period         = 0,  
                                                                                            yr_since_dead  = 0,
                                                                                            Num_DeadTrees  = self.trObject.trees[k].num_DeadTrees,
                                                                                            Dom_species    = 0,
                                                                                            Total_carbon   = self.trObject.trees[k].Total_carbon,
                                                                                            Tot_biomass    = self.trObject.trees[k].Tot_biomass,
                                                                                            Tot_co2        = self.trObject.trees[k].Tot_co2,
                                                                                            Tot_carbon_stems = self.trObject.trees[k].Tot_carbon_stems,
                                                                                            Tot_carbon_roots = self.trObject.trees[k].Tot_carbon_roots,
                                                                                            Tot_co2_stems  = self.trObject.trees[k].Tot_co2_stems,
                                                                                            Tot_co2_roots  = self.trObject.trees[k].Tot_co2_roots,
                                                                                            BGB            = self.trObject.trees[k].BGB,
                                                                                            vol_increment  = 0.,
                                                                                            dead_volume    = self.trObject.trees[k].dead_volume,
                                                                                            dead_co2       = self.trObject.trees[k].dead_co2,
                                                                                            dead_biomass   = self.trObject.trees[k].dead_biomass,
                                                                                            dead_C        = self.trObject.trees[k].dead_C,
                                                                                            R_SPulp        = 0.,
                                                                                            R_PPulp        = 0.,
                                                                                            R_HPulp        = 0.,
                                                                                            R_SSaw         = 0.,
                                                                                            R_PSaw         = 0.,
                                                                                            R_HSaw         = 0.,
                                                                                            Biomass_BAR    = self.trObject.trees[k].Biomass_BAR,
                                                                                            Biomass_LGR    = self.trObject.trees[k].Biomass_LGR,
                                                                                            Biomass_RGE5   = self.trObject.trees[k].Biomass_RGE5,
                                                                                            Biomass_RLT5   = self.trObject.trees[k].Biomass_RLT5, 
                                                                                            unwl           = self.trObject.trees[k].unwl,                   
                                                                                            ufwl           = self.trObject.trees[k].ufwl,     
                                                                                            ucwl           = self.trObject.trees[k].ucwl,
                                                                                            temp           = self.trObject.trees[k].temp,
                                                                                            coord_x        = self.trObject.trees[k].coord_x,
                                                                                            coord_y        = self.trObject.trees[k].coord_y, 
                                                                                            volsum         = self.trObject.trees[k].volsum,
                                                                                            vol_spruce     = self.trObject.trees[k].vol_spruce,
                                                                                            vol_pine       = self.trObject.trees[k].vol_pine,
                                                                                            vol_birch      = self.trObject.trees[k].vol_birch,
                                                                                            vol_others     = self.trObject.trees[k].vol_others,
                                                                                            vol_ROS        = self.trObject.trees[k].vol_ROS,
                                                                                            vol_warm       = self.trObject.trees[k].vol_warm,
                                                                                            ba             = self.trObject.trees[k].ba,
                                                                                            management     = self.trObject.trees[k].management))  
       

## I am using the below trick to set initial value for class method data
        
            vars(self).update(vars(self_template))
##          This dict is used for visualization part            
            GrowthModel.Instances[k] = self.trObject.trees[k].height

##      The below method will update the age for dominant height tree in each plot (Initial dominant height age) 
##      and the plot volume for each period 
##      it was set to 0 when we import the data in the Data class   

        
#        print(self.__str__("299534"))


##   This is initalization for dominant tree age/ we took the mean of ages because the species in each group can have different ages
        ages = []
        for k in self.treeList:
            if self.DERIVED_TREES[str(k)].t_age != 0:  #str(k) in GrowthModel.new_cls_name_list and 
                ages.append(self.DERIVED_TREES[str(k)].t_age)
        self.t_Dtree= np.mean(ages)

##    this is initialization for plot age        
        self.t = float(kwargs["t"])
        if self.t == 0:
            self.t = self.t_Dtree
        
        self.mortality = False
        if 'mortality' in kwargs:
#            self.mortality = float(kwargs["mortality"])
            self.mortality = kwargs["mortality"]
            
        else:
            self.mortality =  True

        self.H40 = float(kwargs["H40"]) 
        self.H0 = self.Dominant_Height()[0]
#            self.H0_1 = self.fH0(Increment=True, t2=self.t1)
                    
#                self.H0 = self.fH0(Increment = False, t2=self.DERIVED_TREES[str(k)].t_age)

        self.N           = self.TPH()
        self.G           = self.fGi()      #G:initial plot basel area
        self.V           = self.fV(0)[0]   #V:initial plot volume
        self.BGB         = self.fCO()[0]            
        self.Tot_co2     = self.fCO()[1]
        self.Tot_biomass = self.fCO()[2]
        self.Total_carbon= self.fCO()[3] 

            
        
                                                    # %%%%%   print purpose %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    def __str__(self,j): 
        """
        Arg: it requires tree_id (str), example: print(self.__str__("299534"))
        Return: Print out the tree object by its elements

        """        
        trees = [k for k in self.DERIVED_TREES.keys()]
        for t in trees: 
            if t==j:
                return 'plot_id\n\t{}\n\ntree_id\n\t{}\n\ntree_sp\n\t{}\n\ndbh\n\t{}\n\nheight\n\t{}\n\ndiameter_class\n\t{}\n\ntree_Factor\n\t{}\n\nSI_spp\n\t{}\n\nSI_m\n\t{}\n\nLAT\n\t{}\n\nspecies\n\t{}\n\nt_age\n\t{}\n\nNum_DeadTrees\n\t{}\n\nDom_species\n\t{}\n'.format(self.DERIVED_TREES[t].plot_id, 
                                   self.DERIVED_TREES[t].tree_id, self.DERIVED_TREES[t].tree_sp, self.DERIVED_TREES[t].dbh, self.DERIVED_TREES[t].height, self.DERIVED_TREES[t].diameter_class,
                                   self.DERIVED_TREES[t].tree_Factor, self.DERIVED_TREES[t].SI_spp,self.DERIVED_TREES[t].SI_m,self.DERIVED_TREES[t].LAT, self.DERIVED_TREES[t].species,
                                   self.DERIVED_TREES[t].t_age, self.DERIVED_TREES[t].Num_DeadTrees, self.DERIVED_TREES[t].Dom_species)
            elif j not in trees:
                return ("Tree_id: "+str(j)+" does not exist in the plot_id: "+ str(self.DERIVED_TREES[t].plot_id)+"!")

                                                    # %%%%%   initial state parameters     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def Initial_state(self):
        return [('Year','Plot id','t','H0', 'SI', 'N','G','V' ,'BGB', 'Tot_co2', 'Tot_biomass', 'Total_carbon'),(self.year, self.plot_id, self.t, self.H0, self.H40, self.N, self.G,self.V, self.BGB, 
                                                                                                                                                                        self.Tot_co2,self.Tot_biomass, self.Total_carbon)]
    
    
                                                    # %%%%%      update required variables      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        
                      

    def update(self,s,mortality, **kwargs):
        """ Updates geometry related parameters and mortality probabilities.

            Returns: dict
                A dictionary with the new attribute values.

                The following attributes are returned:

                {
                "dbh":value,
                "height":value,
                }
                
        """
        
        P = step
        interval = 5
        
        if self.DERIVED_TREES[s].Period < P:
            Period = self.DERIVED_TREES[s].Period + 1
        #elif self.DERIVED_TREES[s].Period == P:
        else:
            Period = self.DERIVED_TREES[s].Period + 0
            
        
        yr_since_dead = self.DERIVED_TREES[s].yr_since_dead + 0    
        DBH = self.NEW_DBH(self.DERIVED_TREES[s], s)
        HEIGHT = self.NEW_HEIGHT(self.DERIVED_TREES[s], s)
        
        species = GrowthModel.DERIVED_TREES[s].species

        for dom_spp in self.Dominant_Height()[1]:
            self.Dom_species = dom_spp

        LitterProduction_tuple = self.fLitter_Production(self.DERIVED_TREES[s],s)
        unwl  = LitterProduction_tuple[0]
        ufwl  = LitterProduction_tuple[1]
        ucwl  = LitterProduction_tuple[2]
        
        if mortality:
             
            mort = self.Mortality_Bollandsas(self.DERIVED_TREES[s],s)
            ## this makes sure the mortality will be held between 0 and 1
            mort_rate = min(1, mort)
            
            survival = self.survival_Bollandsas(self.DERIVED_TREES[s],s)
            
            ba = GrowthModel.update_ba(GrowthModel.DERIVED_TREES[s], DBH)
            
            
            Age = self.DERIVED_TREES[s].t_age + interval
            year = self.DERIVED_TREES[s].year + interval
            

            if survival == 1:        
                n_tree = self.DERIVED_TREES[s].tree_Factor
                Num_DeadTrees = 0
            
            elif survival == 0:
                n_tree = 0
                Num_DeadTrees = self.DERIVED_TREES[s].tree_Factor
                ba = 0
                Period = self.DERIVED_TREES[s].Period + 0
                DBH = self.DERIVED_TREES[s].dbh + 0
                HEIGHT = self.DERIVED_TREES[s].height + 0
                Age = self.DERIVED_TREES[s].t_age + 0
                year = self.DERIVED_TREES[s].year + 0
                yr_since_dead = self.DERIVED_TREES[s].yr_since_dead + 1
            
            else:
                n_tree = self.DERIVED_TREES[s].n_tree * max(survival, 0)
                ## this makes sure the mortality rate cannot be less than zero
                Num_DeadTrees = self.DERIVED_TREES[s].n_tree * max(mort_rate, 0)
                
            """
            When the number of trees goes below 1/2  
            """
            Is_tree_dead = n_tree/self.DERIVED_TREES[s].tree_Factor
            X = 1/(2*self.DERIVED_TREES[s].tree_Factor)
            
            if Is_tree_dead < X:
                n_tree = 0
                ba = 0
                Num_DeadTrees = self.DERIVED_TREES[s].tree_Factor
                Period = self.DERIVED_TREES[s].Period + 0
                yr_since_dead = self.DERIVED_TREES[s].yr_since_dead + 1
                DBH = self.DERIVED_TREES[s].dbh + 0
                HEIGHT = self.DERIVED_TREES[s].height + 0
                Age = self.DERIVED_TREES[s].t_age + 0
                year = self.DERIVED_TREES[s].year + 0
#                GrowthModel.GROWTH.append((s, Num_DeadTrees))
                        
            dead_volume_tuple = self.tree_volume_dead(self.DERIVED_TREES[s], DBH,HEIGHT, Num_DeadTrees, species, aboveBark= True)
#            volsum = dead_volume_tuple[0]
            if species == "spruce":
                dead_volume = dead_volume_tuple[1] 
            elif species == "scots_pine":
                dead_volume = dead_volume_tuple[2]
            elif species == "birch":
                dead_volume = dead_volume_tuple[3]
            elif species == "other_broadleaves":
                dead_volume = dead_volume_tuple[4]
            elif species == "ROS":
                dead_volume = dead_volume_tuple[5]
            elif species == "warm":
                dead_volume = dead_volume_tuple[6]
            
            
            VOLUME = self.tree_volume_function(self.DERIVED_TREES[s], DBH,HEIGHT,n_tree, species, aboveBark= True)
            volsum = VOLUME[0]
            vol_spruce = VOLUME[1]
            vol_pine = VOLUME[2]
            vol_birch = VOLUME[3]
            vol_others = VOLUME[4]
            vol_ROS = VOLUME[5]
            vol_warm = VOLUME[6]
            
            update_dead_C_biomass_co2_tuple = self.Regen_tree_biomass(self.DERIVED_TREES[s],DBH, HEIGHT, species)
            BGB                  =  update_dead_C_biomass_co2_tuple[0] * survival
            Tot_co2              =  update_dead_C_biomass_co2_tuple[1] * survival
            Tot_biomass          =  update_dead_C_biomass_co2_tuple[2] * survival
            Total_carbon         =  update_dead_C_biomass_co2_tuple[3] * survival
            
            dead_co2             =  update_dead_C_biomass_co2_tuple[4] * max(mort_rate, 0) 
            dead_biomass         =  update_dead_C_biomass_co2_tuple[5] * max(mort_rate, 0)
            dead_C               =  update_dead_C_biomass_co2_tuple[6] * max(mort_rate, 0)
            
            Biomass_BAR          =  update_dead_C_biomass_co2_tuple[7] * survival
            Biomass_LGR          =  update_dead_C_biomass_co2_tuple[8] * survival
            Biomass_RGE5         =  update_dead_C_biomass_co2_tuple[9] * survival
            Biomass_RLT5         =  update_dead_C_biomass_co2_tuple[10] * survival
            Tot_carbon_stems     =  update_dead_C_biomass_co2_tuple[11] * survival
            Tot_carbon_roots     =  update_dead_C_biomass_co2_tuple[12] * survival
            Tot_co2_stems        =  update_dead_C_biomass_co2_tuple[13] * survival
            Tot_co2_roots        =  update_dead_C_biomass_co2_tuple[14] * survival

            
                
        else:
            n_tree = self.DERIVED_TREES[s].n_tree
            Num_DeadTrees        = 0
            dead_volume          = 0
            BGB                  =  update_dead_C_biomass_co2_tuple[0]
            Tot_co2              =  update_dead_C_biomass_co2_tuple[1]
            Tot_biomass          =  update_dead_C_biomass_co2_tuple[2]
            Total_carbon         =  update_dead_C_biomass_co2_tuple[3]
            dead_co2             = 0
            dead_biomass         = 0
            dead_C               = 0
            Biomass_BAR          =  update_dead_C_biomass_co2_tuple[7]
            Biomass_LGR          =  update_dead_C_biomass_co2_tuple[8]
            Biomass_RGE5         =  update_dead_C_biomass_co2_tuple[9]
            Biomass_RLT5         =  update_dead_C_biomass_co2_tuple[10]
            Tot_carbon_stems     =  update_dead_C_biomass_co2_tuple[11]
            Tot_carbon_roots     =  update_dead_C_biomass_co2_tuple[12]
            Tot_co2_stems        =  update_dead_C_biomass_co2_tuple[13]
            Tot_co2_roots        =  update_dead_C_biomass_co2_tuple[14]
            
            ba = GrowthModel.update_ba(GrowthModel.DERIVED_TREES[s], DBH)

        ## Calculate volume of trees 
            
            VOLUME = self.tree_volume_function(self.DERIVED_TREES[s], DBH,HEIGHT,n_tree, species, aboveBark= True)
            volsum = VOLUME[0]
            vol_spruce = VOLUME[1]
            vol_pine = VOLUME[2]
            vol_birch = VOLUME[3]
            vol_others = VOLUME[4]
            vol_ROS = VOLUME[5]
            vol_warm = VOLUME[6]
        
        
            
            Age = self.DERIVED_TREES[s].t_age + interval
            year = self.DERIVED_TREES[s].year + interval


        Diameter_Class= self.NEW_Diameter_Class(self.DERIVED_TREES[s], s)
        for i in range(int(self.DERIVED_TREES[s].n_tree)):
            self.DiameterClass.append((Period, Diameter_Class))
            
        management = "none"
        
#        GrowthModel.GROWTH.append((self.DERIVED_TREES[s].DeadList['dead_biomass'],self.DERIVED_TREES[s].DeadList['Period']))                                                                                          
#        GrowthModel.GROWTH.append((s,Period, yr_since_dead))
        attributes = dict(plot_id = self.DERIVED_TREES[s].plot_id,tree_id = self.DERIVED_TREES[s].tree_id,tree_sp = self.DERIVED_TREES[s].tree_sp, dbh = DBH , height = HEIGHT , diameter_class = Diameter_Class,
                          tree_Factor = self.DERIVED_TREES[s].tree_Factor, n_tree = n_tree, year = year, SI_spp = self.DERIVED_TREES[s].SI_spp, altitude_m = self.DERIVED_TREES[s].altitude_m, 
                          SI_m = self.DERIVED_TREES[s].SI_m, LAT = self.DERIVED_TREES[s].LAT,species = species, t_age = Age, Period = Period, yr_since_dead = yr_since_dead, Num_DeadTrees = Num_DeadTrees, 
                          Dom_species = self.Dom_species, BGB = BGB, Tot_co2 = Tot_co2, Total_carbon = Total_carbon, Tot_carbon_stems = Tot_carbon_stems, Tot_carbon_roots = Tot_carbon_roots, 
                          Tot_co2_roots = Tot_co2_roots,  Tot_co2_stems = Tot_co2_stems, Tot_biomass = Tot_biomass, vol_increment = self.DERIVED_TREES[s].vol_increment, dead_volume = dead_volume, dead_co2 = dead_co2, 
                          dead_biomass= dead_biomass, dead_C = dead_C, R_SPulp = self.DERIVED_TREES[s].R_SPulp, R_PPulp = self.DERIVED_TREES[s].R_PPulp, R_HPulp = self.DERIVED_TREES[s].R_HPulp,
                          R_SSaw =  self.DERIVED_TREES[s].R_SSaw , R_PSaw = self.DERIVED_TREES[s].R_PSaw, R_HSaw = self.DERIVED_TREES[s].R_HSaw, Biomass_BAR = Biomass_BAR, Biomass_LGR = Biomass_LGR, 
                          Biomass_RGE5 = Biomass_RGE5, Biomass_RLT5= Biomass_RLT5, unwl = unwl, ufwl = ufwl, ucwl = ucwl, temp = self.DERIVED_TREES[s].temp, coord_x = self.DERIVED_TREES[s].coord_x, coord_y = self.DERIVED_TREES[s].coord_y,
                          volsum = volsum, vol_spruce = vol_spruce, vol_pine = vol_pine ,vol_birch = vol_birch, vol_others= vol_others , vol_ROS = vol_ROS, vol_warm = vol_warm, ba = ba, management = management)
        return   GrowthModel.TreeGenerator(new_cls_name = s , new_parameters= attributes)
        
                                                # %%%%%     Calculate tree volume  for recruited trees     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%           
        
        
    def tree_volume_function(self, dbh,height, n_tree, species, aboveBark= True, **kwargs):
        """
        Calculate stem volume of single trees using Norwegian single tree volume functions for Norway Spruce, pine, Birch and other broadleaved trees
    
        Parameters
        ----------
        s : tree_id (string)
            Each tree object has a key and the values are the attributes of that tree. 
        aboveBark : TRUE or FALSE, optional
            To calculate volume inside Bark [m³/ha]. The default is TRUE.
        **kwargs : TYPE
            dbh : Diameter in breast height in centimeter(cm)including bark
            height: Tree height in meter(m)
    
        Returns
        -------
        Volume for each tree in liters then changed to (m3/ha)
    
        """
        volsum = 0
        vol_spruce = 0
        vol_pine = 0
        vol_birch = 0
        vol_others = 0
        vol_ROS = 0
        vol_warm = 0
        
        dbh = dbh/ 10 # centimeter
        height = height/ 10 # meter
        n_tree = n_tree
        sp = species
        if n_tree != 0:
            if sp == "spruce":
                
                if aboveBark:
                    a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4 = 0.52, 0.02403, 0.01463, -0.10983, 0.15195, -31.57, 0.0016, 0.0186, 0.63, -2.34, 3.2, 10.14, 0.0124, 0.03117, -0.36381, 0.28578           
                else:
                    a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4 = 0.38, 0.02524, 0.01269, -0.07726, 0.11671, -27.19, 0.0073, -0.0228, 0.5667, -1.98, 2.75, 8.66, 0.01218, 0.02976, -0.31373, 0.25452
                
                if dbh <= 10:
                    vol_spruce = (( a0 + a1 * dbh * dbh * height + a2 * dbh * height * height + a3 * height * height + a4 * dbh * height)/1000) *  n_tree
                elif dbh > 10 and dbh <= 13:
                    vol_spruce = ((b0 + b1 * dbh * height * height + b2 * height * height + b3 * dbh * height + b4 * height + b5 * dbh)/1000) *  n_tree
                else:
                    vol_spruce = ((c0 + c1 * dbh * dbh * height + c2 * dbh * height * height + c3 * height * height + c4 * dbh * height)/1000) *  n_tree
                
            elif sp == "scots_pine":  
                if aboveBark:
                    a0, a1, a2, b0, b1, b2, b3 = 2.9121, 0.039994, - 0.001091, 8.6524, 0.076844, 0.031573, 0
                else:
                    a0, a1, a2, b0, b1, b2, b3 = 2.2922, 0.040072, 0.00216, -3.5425, 0.128182, 0.028268, 0.008216
                    
                if dbh <= 11:
                    vol_pine = max(0, (((a0 + a1 * dbh * dbh * height + a2 * dbh * height * height)/1000) *  n_tree))
                else:
                    vol_pine = max(0, (((b0 + b1 * dbh * dbh + b2 * dbh * dbh * height + b3 * dbh * height + height)/1000) *  n_tree))
    
                    
            elif sp == "birch":
                
                B = 1.046 * dbh
                
                if aboveBark:
                    a0, a1, a2, a3, a4, a5 = -1.25409 , 0.12739, 0.03166, 0.0009752, -0.01226, -0.004214
                else:
                    a0, a1, a2, a3, a4, a5 = -1.48081 , 0.16945, 0.01834, 0.01018, -0.0451 , 0
                    
                vol_birch = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)/1000) *  n_tree))
    
    #        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
            
            elif sp == "other_broadleaves":
                 
                B = 1.046 * dbh
                
                if aboveBark:
                    a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                    #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
                else:
                    a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
                #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
                vol_others = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))
            
            elif sp == "ROS":
                 
                B = 1.046 * dbh
                
                if aboveBark:
                    a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                    #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
                else:
                    a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
                #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
                vol_ROS = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))      
            
            elif sp == "warm":
                 
                B = 1.046 * dbh
                
                if aboveBark:
                    a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                    #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
                else:
                    a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
                #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
                vol_warm = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))      
            
            volsum = vol_spruce + vol_pine + vol_birch + vol_others + vol_ROS + vol_warm

            return volsum, vol_spruce, vol_pine, vol_birch , vol_others, vol_ROS , vol_warm
        
        else:
            volsum, vol_spruce, vol_pine, vol_birch , vol_others, vol_ROS , vol_warm = 0., 0. , 0., 0. , 0., 0. , 0.
            
            return volsum, vol_spruce, vol_pine, vol_birch , vol_others, vol_ROS , vol_warm

                                                # %%%%%     Calculate tree volume  for dead trees     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%           
        
        
    def tree_volume_dead(self, dbh,height, n_tree, species, aboveBark= True, **kwargs):
        """
        Calculate stem volume of single trees using Norwegian single tree volume functions for Norway Spruce, pine, Birch and other broadleaved trees
    
        Parameters
        ----------
        s : tree_id (string)
            Each tree object has a key and the values are the attributes of that tree. 
        aboveBark : TRUE or FALSE, optional
            To calculate volume inside Bark [m³/ha]. The default is TRUE.
        **kwargs : TYPE
            dbh : Diameter in breast height in centimeter(cm)including bark
            height: Tree height in meter(m)
    
        Returns
        -------
        Volume for each tree in liters then changed to (m3/ha)
    
        """
        volsum = 0
        vol_spruce = 0
        vol_pine = 0
        vol_birch = 0
        vol_others = 0
        vol_ROS = 0
        vol_warm = 0
        
        dbh = dbh/ 10 # centimeter
        height = height/ 10 # meter
        n_tree = n_tree
        sp = species
        
        if sp == "spruce":
            
            if aboveBark:
                a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4 = 0.52, 0.02403, 0.01463, -0.10983, 0.15195, -31.57, 0.0016, 0.0186, 0.63, -2.34, 3.2, 10.14, 0.0124, 0.03117, -0.36381, 0.28578           
            else:
                a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4 = 0.38, 0.02524, 0.01269, -0.07726, 0.11671, -27.19, 0.0073, -0.0228, 0.5667, -1.98, 2.75, 8.66, 0.01218, 0.02976, -0.31373, 0.25452
            
            if dbh <= 10:
                vol_spruce = (( a0 + a1 * dbh * dbh * height + a2 * dbh * height * height + a3 * height * height + a4 * dbh * height)/1000) *  n_tree
            elif dbh > 10 and dbh <= 13:
                vol_spruce = ((b0 + b1 * dbh * height * height + b2 * height * height + b3 * dbh * height + b4 * height + b5 * dbh)/1000) *  n_tree
            else:
                vol_spruce = ((c0 + c1 * dbh * dbh * height + c2 * dbh * height * height + c3 * height * height + c4 * dbh * height)/1000) *  n_tree
            
        elif sp == "scots_pine":  
            if aboveBark:
                a0, a1, a2, b0, b1, b2, b3 = 2.9121, 0.039994, - 0.001091, 8.6524, 0.076844, 0.031573, 0
            else:
                a0, a1, a2, b0, b1, b2, b3 = 2.2922, 0.040072, 0.00216, -3.5425, 0.128182, 0.028268, 0.008216
                
            if dbh <= 11:
                vol_pine = max(0, (((a0 + a1 * dbh * dbh * height + a2 * dbh * height * height)/1000) *  n_tree))
            else:
                vol_pine = max(0, (((b0 + b1 * dbh * dbh + b2 * dbh * dbh * height + b3 * dbh * height + height)/1000) *  n_tree))

                
        elif sp == "birch":
            
            B = 1.046 * dbh
            
            if aboveBark:
                a0, a1, a2, a3, a4, a5 = -1.25409 , 0.12739, 0.03166, 0.0009752, -0.01226, -0.004214
            else:
                a0, a1, a2, a3, a4, a5 = -1.48081 , 0.16945, 0.01834, 0.01018, -0.0451 , 0
                
            vol_birch = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)/1000) *  n_tree))

#        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        
        elif sp == "other_broadleaves":
             
            B = 1.046 * dbh
            
            if aboveBark:
                a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
            else:
                a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
            #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
            vol_others = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))
        
        elif sp == "ROS":
             
            B = 1.046 * dbh
            
            if aboveBark:
                a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
            else:
                a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
            #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
            vol_ROS = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))      
        
        elif sp == "warm":
             
            B = 1.046 * dbh
            
            if aboveBark:
                a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
            else:
                a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
            #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
            vol_warm = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))      
        
        
        volsum = vol_spruce + vol_pine + vol_birch + vol_others + vol_ROS + vol_warm

        return volsum, vol_spruce, vol_pine, vol_birch , vol_others, vol_ROS , vol_warm
        

                                                    # %%%%%     update Biomass       %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        
    
    
    def update_biomass(self,D,H,SP,s):
        
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
        dbh : Diameter in breast height in centimeter(cm) including bark
        height: Tree height in meter(m)
        sp: tree species (Norway spruce, Scots Pine, Birch)
        
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
        carbon: carbon stored by tree in kg (equivalent mass of carbon)
        co2: CO2 equivalent of tree biomass

        """

        Carbon_conversion_factor= 0.5
        CO2_Fraction = 3.67
        dbh = D / 10 # centimeter
        #height = H / 10 # meter
        height = H
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

             
            bg = (exp((0.32308**2) / 2 + 4.58761 + (dbh*10) / ((dbh*10) + 138) * 10.44035))/1000 # blow ground biomass / Petterson and Stahl 2006 Root limit 2 mm
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

        
        Tot_biomass = Biomass_ST  + Biomass_LGR + Biomass_DGR + Biomass_STU + Biomass_BGB #+ Biomass_BAR + Biomass_RGE5 + Biomass_RLT5
        Total_carbon = Tot_biomass * Carbon_conversion_factor
        Tot_co2 = Total_carbon * CO2_Fraction
        Tot_carbon_stems = Biomass_ST*Carbon_conversion_factor
        Tot_carbon_roots = (Biomass_LGR + Biomass_DGR + Biomass_STU + Biomass_BAR + Biomass_RGE5 + Biomass_RLT5)*Carbon_conversion_factor
        Tot_co2_stems = Tot_carbon_stems * CO2_Fraction
        Tot_co2_roots = Tot_carbon_roots * CO2_Fraction
        
        
        attributes = dict(plot_id = self.DERIVED_TREES[s].plot_id,tree_id = self.DERIVED_TREES[s].tree_id,tree_sp = self.DERIVED_TREES[s].tree_sp, year = self.DERIVED_TREES[s].year, dbh = self.DERIVED_TREES[s].dbh , height = self.DERIVED_TREES[s].height, 
                          diameter_class = self.DERIVED_TREES[s].diameter_class, tree_Factor = self.DERIVED_TREES[s].tree_Factor, n_tree = self.DERIVED_TREES[s].n_tree, SI_spp = self.DERIVED_TREES[s].SI_spp,altitude_m = self.DERIVED_TREES[s].altitude_m, 
                          SI_m = self.DERIVED_TREES[s].SI_m, LAT = self.DERIVED_TREES[s].LAT, species = self.DERIVED_TREES[s].species, t_age = self.DERIVED_TREES[s].t_age , Period = self.DERIVED_TREES[s].Period, yr_since_dead =self.DERIVED_TREES[s].yr_since_dead, Num_DeadTrees =  self.DERIVED_TREES[s].Num_DeadTrees, 
                          Dom_species = self.DERIVED_TREES[s].Dom_species, BGB = Biomass_BGB, Tot_co2 = Tot_co2, Tot_biomass = Tot_biomass, Total_carbon = Total_carbon, Tot_carbon_stems = Tot_carbon_stems , Tot_carbon_roots = Tot_carbon_roots, Tot_co2_stems = Tot_co2_stems, 
                          Tot_co2_roots = Tot_co2_roots, vol_increment = self.DERIVED_TREES[s].vol_increment, dead_volume = self.DERIVED_TREES[s].dead_volume, dead_co2 = self.DERIVED_TREES[s].dead_co2, dead_biomass= self.DERIVED_TREES[s].dead_biomass, 
                          dead_C = self.DERIVED_TREES[s].dead_C, R_SPulp = self.DERIVED_TREES[s].R_SPulp, R_PPulp = self.DERIVED_TREES[s].R_PPulp, R_HPulp = self.DERIVED_TREES[s].R_HPulp, R_SSaw =  self.DERIVED_TREES[s].R_SSaw , R_PSaw = self.DERIVED_TREES[s].R_PSaw, 
                          R_HSaw = self.DERIVED_TREES[s].R_HSaw, Biomass_BAR = Biomass_BAR, Biomass_LGR = Biomass_LGR, Biomass_RGE5 = Biomass_RGE5, Biomass_RLT5= Biomass_RLT5, unwl = self.DERIVED_TREES[s].unwl, ufwl = self.DERIVED_TREES[s].ufwl, ucwl = self.DERIVED_TREES[s].ucwl, 
                          temp = self.DERIVED_TREES[s].temp, coord_x = self.DERIVED_TREES[s].coord_x, coord_y = self.DERIVED_TREES[s].coord_y, volsum = self.DERIVED_TREES[s].volsum, vol_spruce = self.DERIVED_TREES[s].vol_spruce, vol_pine = self.DERIVED_TREES[s].vol_pine,
                          vol_birch = self.DERIVED_TREES[s].vol_birch, vol_others= self.DERIVED_TREES[s].vol_others , vol_ROS = self.DERIVED_TREES[s].vol_ROS, vol_warm = self.DERIVED_TREES[s].vol_warm, ba = self.DERIVED_TREES[s].ba , management = self.DERIVED_TREES[s].management)
        
        return   GrowthModel.TreeGenerator(new_cls_name = s , new_parameters= attributes)
    
    
                                                # %%%%%      update tree age      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    
    def tree_age(self,s):
        """ Calculate the age of the dominant height tree in each plot and replace it with the initial age set to zero
            (age of the dominant trees to calculate the siteindex)
        """
        ageint = [x for x in range(1,1000,1)]
        htd1 = self.Dominant_Height()[0] - 1.3
#        self.GROWTH.append(htd1) 
        tref= 40
        t1=0
        sp= self.DERIVED_TREES[s].species
        SI = self.DERIVED_TREES[s].SI_m
        Ht = self.DERIVED_TREES[s].height

        if sp == "spruce": 
            b1,b2,b3= 18.9206,5175.18,1.1576            
            for a in range (1, len(ageint)):                
                X0 = 0.5 * (SI - 1.3 - b1 + sqrt((SI - 1.3 - b1) ** 2 + 4 * b2 * (SI - 1.3) * tref ** -b3))
                h1 = (b1 + X0) / (1 + (b2 / X0 * ageint[a] ** (-b3))) 
                if (h1 - 1.3)  > htd1:
                    t1 = ageint[a]
                    break
           
        elif sp == "scots_pine": 
            b1,b2,b3= 12.8361,3263.99,1.1758
            for a in range (1, len(ageint)):                
                X0 = 0.5 * (SI - 1.3 - b1 + sqrt((SI - 1.3 - b1) ** 2 + 4 * b2 * (SI - 1.3) * tref ** -b3))
                h1 = (b1 + X0) / (1 + (b2 / X0 * ageint[a] ** (-b3)))
                if (h1 - 1.3)  > htd1:
                    t1 = ageint[a]                    
                    break                
# Birch and broadleaves                
#        elif  sp in birch_species or sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        else:
            b1,b2,K= 394,1.387,7
            for a in range (1, len(ageint)): 
                X0 = sqrt((SI - 1.3 -(b1/(K**b2))) ** 2 + 4 * b1 * (SI - 1.3) / (tref ** b2))
                h1 = (SI - 1.3 +(b1/(K**b2))+ X0) / (2 + 4 * b1 *  ageint[a]  ** (- b2)/(SI - 1.3 -(b1/(K**b2))+ X0))
                if (h1-1.3)  > htd1:
                    t1 = ageint[a]
                    break

        if t1 <= 11:
            t1 = 11
        elif t1 > 400:
            t1 = 400
        else:                   
            t1 = ageint[a]
                
#        self.GROWTH.append((t1))                       
        return t1
    


                                                # %%%%%     Calculate New DBH      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    
    
    def NEW_DBH(self,k,**kwargs):
        
        """compute the new tree dbh calculated for Norway Spruce, Pine and Birch according to the diameter increment model

        Returns: float
        """
        
        N = self.TPH()
#        
        G = self.fGi(self.DERIVED_TREES[k])
        
        Dg = self.fDg(self.DERIVED_TREES,N,G)
        
        Ht = GrowthModel.DERIVED_TREES[k].height

#        GrowthModel.GROWTH.append(Dg)
        if DiameterGrowth_model == "Weibull model":
            INC1 = self.I5yr_fWeibull(GrowthModel.DERIVED_TREES[k],Dg,k)
        elif DiameterGrowth_model == "matrix model": 
            INC1 = self.fd13_increment(GrowthModel.DERIVED_TREES[k],k)

               
        DBH = GrowthModel.DERIVED_TREES[k].dbh
        
        if INC1 > 100:    # a 5-year increment should not go over 100 mm 
            INC1 = 100
        if INC1 < 0:
            INC1 = 0
            
#        if Ht > 70 and self.t <=:    # If height threshold of 7 m is reached for young stands
#            INC1 = 0
#        self.GROWTH.append((k, DBH, INC1)) 
        # if DBH >= 50:
        #     INC1 
        # else:
        #     INC2 
            
        # if INC1 > 3*INC2 :

        # return DBH + INC2
#        GrowthModel.GROWTH.append((k,INC1))
        return DBH + INC1
    
                                                # %%%%%      Calculate New Height      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        
    
        
    def NEW_HEIGHT(self,k,**kwargs):
        """Calculate the new tree height calculated for Norway Spruce, Pine and Birch according to the height increment models

        Returns: float
        """

        POT = self.POT(self.DERIVED_TREES[k],k)
#        self.GROWTH.append(POT)
        sp= self.DERIVED_TREES[k].species
        
        Ht = GrowthModel.DERIVED_TREES[k].height
        
        if sp == "spruce" or sp == "scots_pine":
            ih = self.Height_Modifier(self.DERIVED_TREES[k],k)
            INC = POT * ih * 10   ## convert it to dm
#        elif sp == "birch" or sp == "other_broadleaves" or sp == "ROS" or sp == "warm":
        else:
            INC = POT * 10 ## convert it to dm
        
        if INC > 300:   # a 5-year increment should not go over 3 m (60 cm/year)
            INC = 300
        if INC < 0:
            INC = 0
#        if Ht > 70 and self.t <= :    # If height treshold of 7 m is reached  for young stands
#            INC = 0
            
#        self.GROWTH.append((Ht, INC))
        
        return round(Ht+INC)
    
                                                # %%%%%      Calculate New Diameter class     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        
    
    
    def NEW_Diameter_Class(self, s, **kwargs):
        """Calculate the new diameter class based on the new dbh

        Returns: int
        """
        self.DBH = self.NEW_DBH(self.DERIVED_TREES[s], s)
        
        a= 50
        b= 100
        c = 5
        Diameteric_Class= 5
        for i in range (50, 1049, 50):
            if self.DBH >= a and  self.DBH < b:
                Diameteric_Class = c
            else:
                c+= 5
                a+=50
                b+=50
#        next
#        self.GROWTH.append(Diameteric_Class)  
        return Diameteric_Class


                                                # %%%%%     Calculate Dominant height     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

            
    def H0T(self, s, Increment = False, **kwargs):
        """
        Calculates dominant height calculated according to eq.1 in Sharma et al.(2011) and 

        Parameters
        ----------
        sp : tree species type
            DESCRIPTION.
        Increment : TYPE, optional
            DESCRIPTION. The default is False.
        H0: Dominant height(m) at breast height (1.3 m above ground level)
        t1: initial age for the dominant height (years)
        t2: age at the second point in time (years) 

        Returns
        -------
        Dominant height at t2(m)

        """
             
        if not Increment:
            t2 = self.DERIVED_TREES[s].t_age + 5

        else:
            t2 = kwargs["t2"]
           
        t1 = self.DERIVED_TREES[s].t_age
        
        sp= self.DERIVED_TREES[s].species
        if sp == "spruce" or sp == "scots_pine":
            
            if sp == "spruce":
                b1,b2,b3= 18.9206,5175.18,1.1576 
            else:
#            elif sp == "scots_pine":
                b1,b2,b3= 12.8361,3263.99,1.1758 

            H0 = self.Dominant_Height()[0] - 1.3
            #H0 = self.DERIVED_TREES[s].height/10 - 1.3
        
            X0 = 0.5 * (H0 - b1 + sqrt((H0 - b1) ** 2 + 4 * b2 *
                                            (H0 ) * t1 ** -b3))
            H0_m = (b1 + X0) / (1 + (b2 / X0 * (t2 ** (-b3)))) + 1.3
            
#        elif sp in birch_species or sp in other_broadleaves_species or sp in ROS_species or sp in warm_species : 
        else:
            
            b1,b2,k = 394, 1.387, 7
            d1 = b1 / (k**b2)
            H0 = self.Dominant_Height()[0] - 1.3
            #H0 = self.DERIVED_TREES[s].height/10 - 1.3
            
            X0 = sqrt(( H0 - d1 )**2 + 4 * b1 * H0 / (t1)**b2 ) 
            
            H0_m = (H0 + d1 + X0 ) / ( 2 + 4 * b1 * ( t2 ) ** ( -1 * b2 ) / ( H0 - d1 + X0 ) ) + 1.3
#        self.GROWTH.append((H0))       
        return H0_m
        
                                                # %%%%%      Calculate Potential height increment      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def POT(self, s, **kwargs):
        """Calculating potential height increment
        DHT1 = self.fH0(t2 = self.t1) : Initial dominant height at age t1
        DHT2 = self.fH0(t2 = self.t1 + 5 yrs): Projected dominant height at age t2
        """


        DHT1= self.H0T(self.DERIVED_TREES[s], s, Increment=True, t2 = self.DERIVED_TREES[s].t_age)
        DHT2= self.H0T(self.DERIVED_TREES[s], s, Increment=True, t2 = self.DERIVED_TREES[s].t_age +5)
        # self.GROWTH.append((DHT1,DHT2))
        POT = DHT2 - DHT1
#        self.GROWTH.append(POT)
        return POT
    
                                                # %%%%%     survival_Bollandsas     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def survival_Bollandsas(self, s):
        """
        Calculating survival rate from Bollandsås et al. (2008) with updated parameters (Thurner et al., 2016) 

        Parameters
        ----------
        s : species type
            DESCRIPTION.

        Returns
        -------
        survival rate

        """
        
        dbh = self.DERIVED_TREES[s].dbh                               ## Diameter at breast height (cm)
        BA = self.fGi(self.DERIVED_TREES[s])                         ## plot basal area (m2ha-1)
        N = self.TPH()
        Dg = self.fDg(self.DERIVED_TREES,N,BA)
        
        if DiameterGrowth_model == 'Weibull model':
            I5yr = self.I5yr_fWeibull(GrowthModel.DERIVED_TREES[s],Dg,s)
#        elif DiameterGrowth_model == 'matrix model':  
        elif DiameterGrowth_model == "matrix model":
            I5yr = self.fd13_increment(GrowthModel.DERIVED_TREES[s],s)     
        
        sp= self.DERIVED_TREES[s].species
        
        if sp == "spruce" : 
#            gamma0,gamma1,gamma2,gamma3, w = -2.438 , -0.02345 , 0.00003501 , 0.05057, 50      ## parameters are taken from Thurner et al. (2016)
            gamma0,gamma1,gamma2,gamma3, w = -2.4916 , -0.02 , 0.000032 , 0.0308, 50          ## parameters are taken from Bollandsås et al. (2008) 
        elif sp == "scots_pine":
#            gamma0,gamma1,gamma2,gamma3 ,w = -1.952 , -0.0286 , 0.00003746 , 0.06147 , 50
            gamma0,gamma1,gamma2,gamma3 ,w = -1.8079 , -0.0267 , 0.000033 , 0.055 , 50
        elif sp == "birch":
#            gamma0,gamma1,gamma2,gamma3, w = -2.216 , -0.01098 , 0.00001802 , 0.02183 , 50
            gamma0,gamma1,gamma2,gamma3, w = -2.1876 , -0.0157 , 0.000027 , 0.0295 , 50
#        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        else:
#            gamma0,gamma1,gamma2,gamma3, w = -1.551 , -0.011 , 0.000014 , 0.016 , 50
            gamma0,gamma1,gamma2,gamma3, w = -1.5512 , -0.0111 , 0.000014 , 0.0159 , 50
            
            
        # the probability that a tree of species group i and diameter class j died during the interval t to t+p
        Mij = (1 + exp(-1 * (gamma0 + (gamma1 * dbh) + (gamma2 * dbh * dbh) + (gamma3 * BA))))** (-1.)
        # the probability that a tree of species group i in diameter class j grows into diameter class j+1 during the time interval p.
        bij = (I5yr / w)
        # the probability that a tree of species i will remain in diameter class j between t and t+p
        ait = 1 - bij - Mij
        #
        if ait < 0:
            ait = 0
        
        if Mij < 0:
            Mij = 0.0
        elif Mij > 1:
            Mij = 1.0
        else:
            Mij = Mij

        # the probability that a tree of species i will stay alive in the plot s
        ais = 1 - Mij
#        GrowthModel.GROWTH.append((Mij))
        return ais
    
    
                                                # %%%%%     survival_Eid_Tuhus     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def survival_Eid_Tuhus(self, s):
        """
        Calculating survival rate from Eid & Tuhus 

        Parameters:
            SI_m(H40): Site index of spruce (m)
            dbh = diameter breast height (mm)
            LAT = Latitude (degree)
            BAL = basal area of trees (c) larger than subject tree(k) (m2h-1)
            BA  = plot basal area (m2h-1)

        Returns: mm per 5 yr
        """
        sp= self.DERIVED_TREES[s].species
        dbh = self.DERIVED_TREES[s].dbh
        BAL = self.BAL(self.DERIVED_TREES[s],s)
        SI  = self.DERIVED_TREES[s].SI_m
        BA = self.fGi(self.DERIVED_TREES[s])
        BA_spruce = GrowthModel.BA_spruce(GrowthModel.DERIVED_TREES)[0]
#        BA_pine   = GrowthModel.BA_pine(GrowthModel.DERIVED_TREES)[0]
        # BA_Birch  = GrowthModel.BA_birch(GrowthModel.DERIVED_TREES)[0]
        # BA_OtherBroadleaves = GrowthModel.BA_OtherBroadleaves(GrowthModel.DERIVED_TREES)
        
        if sp == "spruce": 
            theta0, theta1, theta2, theta3, theta4 = 8.0599 , - 6.702 , - 0.0281 , - 0.0264, - 0.0132
            growth_TPH = (1 + exp(-1 *(theta0 + (theta1 * (dbh)** -1) + (theta2 * BAL) + (theta3 * SI) + (theta4 * (BA_spruce/BA)))))** -5
        elif sp == "scots_pine":
            theta0, theta1, theta2, theta3, theta4 = 8.4904 , -14.266, - 0.0462 , - 0.0761 , 0
            growth_TPH = (1 + exp(-1 *(theta0 + (theta1 * (dbh)** -1) + (theta2 * BAL) + (theta3 * SI) )))** -5
        elif sp == "birch":
            theta0, theta1, theta2, theta3, theta4 = 4.8923 , -2.528, 0, 0 , 0 
            growth_TPH = (1 + exp(-1 *(theta0 + (theta1 * (dbh)** -1))))** -5
#        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        else:
            theta0, theta1, theta2, theta3, theta4 = 5.1575 , -7.3544, - 0.0199, 0, 0 
            growth_TPH = (1 + exp(-1 *(theta0 + (theta1 * (dbh)** -1) + (theta2 * BAL))))** -5
            
        return growth_TPH
    
                                                # %%%%%      Mortality_Bollandsas     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    
    def Mortality_Bollandsas(self, s):
        """
        Calculating mortality rate from Bollandsås et al. (2008) with updated parameters (Thurner et al., 2016) 

        Parameters
        ----------
        s : Species type
            DESCRIPTION.

        Returns
        -------
        mortality rate 

        """
        
        dbh = self.DERIVED_TREES[s].dbh             ## Diameter at breast height (mm)
        BA = self.fGi(self.DERIVED_TREES[s])        ## plot basal area (m2ha-1)

        sp= self.DERIVED_TREES[s].species
        
        if sp == "spruce" : 
#            gamma0,gamma1,gamma2,gamma3, w = -2.438 , -0.02345 , 0.00003501 , 0.05057, 50                 ## parameters are taken from Thurner et al. (2016)
            gamma0,gamma1,gamma2,gamma3, w = -2.4916 , -0.02 , 0.000032 , 0.0308, 50                     ## parameters are taken from Bollandsås et al. (2008) 
        elif sp == "scots_pine":
#            gamma0,gamma1,gamma2,gamma3 ,w = -1.952 , -0.0286 , 0.00003746 , 0.06147 , 50
            gamma0,gamma1,gamma2,gamma3 ,w = -1.8079 , -0.0267 , 0.000033 , 0.055 , 50
        elif sp == "birch":
#            gamma0,gamma1,gamma2,gamma3, w = -2.216 , -0.01098 , 0.00001802 , 0.02183 , 50
            gamma0,gamma1,gamma2,gamma3, w = -2.1876 , -0.0157 , 0.000027 , 0.0295 , 50
#        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        else:
#            gamma0,gamma1,gamma2,gamma3, w = -1.551 , -0.011 , 0.000014 , 0.016 , 50
            gamma0,gamma1,gamma2,gamma3, w = -1.5512 , -0.0111 , 0.000014 , 0.0159 , 50
            
        
        Mij = (1 + exp(-1 * (gamma0 + (gamma1 * dbh) + (gamma2 * dbh * dbh) + (gamma3 * BA))))** (-1.)

#        GrowthModel.GROWTH.append((Mij))
        if Mij < 0:
            Mij = 0
        elif Mij > 1:
            Mij = 1
        else:
            Mij = Mij
        return Mij

                                                # %%%%%     fMic    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def fMic(self, **kwargs):
        

        V_spruce = sum([(self.DERIVED_TREES[k].vol_spruce + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
                
        V_pine = sum([(self.DERIVED_TREES[k].vol_pine + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
                
        vol_birch = sum([(self.DERIVED_TREES[k].vol_birch + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)]) 
        vol_others = sum([(self.DERIVED_TREES[k].vol_others + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        vol_ROS = sum([(self.DERIVED_TREES[k].vol_ROS + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        vol_warm =  sum([(self.DERIVED_TREES[k].vol_warm + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_others = vol_birch + vol_others + vol_ROS + vol_warm
        
        if (V_spruce + V_pine + V_others) !=0:
            V_trees = V_spruce + V_pine + V_others
        else:
            V_trees = 0.001                
               
        if V_spruce >= V_pine and V_spruce >= V_others:
            Mic_type = "High_spruce"
        elif V_pine > V_spruce and V_pine >= V_others:
            Mic_type = "High_pine"
        elif V_others > V_spruce and V_others > V_pine :
            Mic_type = "broadleaf"
        
        return Mic_type

    
                                                # %%%%%    fCO    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def fCO(self, **kwargs):
        pass  
    
                                                # %%%%%      fHO     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def fH0(self,Increment = False, **kwargs):
        pass

                                                # %%%%%      fPOT    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    
    def fPOT(self, **kwargs):
        pass

                                                # %%%%%     fGi     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    
    # def fID(self, **kwargs):
    #     return self.plot_id

    def fGi(self, **kwargs):
        """
        == BA        
        Calculate basal area for each plot per hectare, to test in main print(GrowthModel.fGi())
        Return: plot basal area (m2ha-1)
        """

        BAL = sum([(self.DERIVED_TREES[k].ba * self.DERIVED_TREES[k].n_tree) for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0])
           
        return BAL  
    
                                                # %%%%%      BAL     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    
    def BAL(self,s):
        """
        calculate Basal-Area-in-Larger Trees, for example : BAL("379828")
        Return: (m2 ha−1)
        """        
        trees = [k for k in self.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0]
        BAL=0
        for c in trees:
            if GrowthModel.ba(self.DERIVED_TREES[c],c) > GrowthModel.ba(self.DERIVED_TREES[c],s) and s!=c:
                basal = GrowthModel.ba(self.DERIVED_TREES[c],c)*self.DERIVED_TREES[c].n_tree
                BAL+=basal
        return BAL

                                                # %%%%%      fGp     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def fGp(self, i, **kwargs):
        pass
    
                                                # %%%%%      fV     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def fV(self, i, **kwargs):
        pass


                                                # %%%%%     fProducts     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%       


    def fProducts(self, i, **kwargs):
        pass


    
                                                # %%%%%      fDg     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def fDg(self, N, G):
        """ Mean basal area diameter of plot p or Mean quadratic diameter (cm)
        Parameters:
            G: plot basal area (m2 ha-1)
            N = number of tree per hectar

        Returns: Mean basal area diameter
        """ 
        if N == 0: N = 0.01 

        Dg = sqrt(G * 4 / (max(N, .1) * pi)) * 100 #if N != 0 else 0   ## 100 is convering meter to cm
        
        return Dg

                                                # %%%%%      ba     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def ba(self,k):
        """        
        Calculate basal area for each tree, to test in main: print(GrowthModel.ba('138243'))
        Return: tree basal area (m2)
        """

        return pi*(self.DERIVED_TREES[k].dbh/2000)**2

                                                # %%%%%      update ba     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    def update_ba(self, dbh):
        """        
        update basal area for given dbh, to test in main: print(GrowthModel.update_ba(50))
        dbh = mm
        Return: tree basal area (m2)
        """

        return pi*(dbh/2000)**2
        
                                                # %%%%%      fd13_increment     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    
    def fd13_increment(self,k,**kwargs):
        
        """
        Calculate diameter growth according to eq.6 in Bollandsas et al.(2008).
        Parameters:
            SI_m(H40): Site index of spruce (m)
            dbh = diameter breast height (mm)
            LAT = Latitude (degree)
            BAL = basal area of trees (c) larger than subject tree(k) (m2h-1)
            BA  = plot basal area (m2h-1)

        Returns: mm per 5 yr
        """
        sp= self.DERIVED_TREES[k].species
        if sp == "spruce": 
            theta0, theta1, theta2, theta3, theta4, theta5, theta6, theta7 = 17.839 , 0.0476, - 0.00011585, 0 , - 0.3412 , 0.906 , - 0.024, - 0.268
        elif sp == "scots_pine":
            theta0, theta1, theta2, theta3, theta4, theta5, theta6, theta7 = 25.543 , 0.0251, - 0.0000566, 0 , - 0.216 , 0.698 , - 0.123, - 0.336
        elif sp == "birch":
            theta0, theta1, theta2, theta3, theta4, theta5, theta6, theta7 = 11.808 , 0, - 0.00009616, - 0.00000009585 , 0 , 0.519 , - 0.152, - 0.161
#        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        else:
            theta0, theta1, theta2, theta3, theta4, theta5, theta6, theta7 = 2.204 , 0.063, - 0.0000832, 0 , 0 , 0.359 , - 0.177, 0
            
            
        dbh = self.DERIVED_TREES[k].dbh
        BAL = self.BAL(self.DERIVED_TREES[k],k)
        SI  = self.DERIVED_TREES[k].SI_m
        BA = self.fGi(self.DERIVED_TREES[k])
        LAT = self.DERIVED_TREES[k].LAT
        
        growth_d13 = round(theta0 + (theta1 * dbh) + (theta2 * (dbh ** 2)) + (theta3 * (dbh ** 3)) + (theta4 * BAL) + (theta5 * SI) + (theta6 * BA) + (theta7 * LAT))

        return growth_d13
        
                                                # %%%%%      I5yr_fWeibull     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

        
    def I5yr_fWeibull(self, Dg, k):  # check if dbh and Dg are in correct unit(mm or cm)
        """
        Calculate diameter growth calculated according to eq.6 in Bollandsas and Erik Næsset (2009).
        A two-parameter weibull function is uded to model the diameter distribution.
        B1 and B2 : scale and shape (skewness) parameters, respectively.
        
        Parameters:
            SI_m(H40): Site index of spruce (m)
            dbh = diameter breast height (mm)
            LAT = Latitude (degree)
            BA  = plot basal area (m2h-1)

        Returns: mm per 5 yr
        """
        sp= self.DERIVED_TREES[k].species
        
        if sp == "spruce": 
            B1, B2,gamma0,gamma1,gamma2,gamma3,gamma4 =1.3615,503.63,1824106,0.5574,1.1997, -0.5254, - 1.6726
        elif sp == "scots_pine":
            B1, B2,gamma0,gamma1,gamma2,gamma3,gamma4 =1.3548,443.85,2586.91,0.4245,0.8743, -0.4219, 0
        elif sp == "birch":
            B1, B2,gamma0,gamma1,gamma2,gamma3,gamma4 =1.0085,2651.94,49080456,0.6251,1.0225, -0.3011, - 2.3007
#        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        else:
            B1, B2,gamma0,gamma1,gamma2,gamma3,gamma4 =1.4168,646.02,6528,0.3354,0.5562, -0.3362, 0

        dbh = self.DERIVED_TREES[k].dbh    
        SI  = self.DERIVED_TREES[k].SI_m
        LAT = self.DERIVED_TREES[k].LAT
        G = self.fGi(self.DERIVED_TREES[k])
        

        I5yr = round(((B1/B2)*((dbh/B2) ** (B1-1)) * exp(-((dbh/B2)** B1)))*gamma0*(((dbh/10)/Dg)** gamma1)*(SI ** gamma2)*(G ** gamma3) * (LAT ** gamma4))
        
        return I5yr
    
                                                # %%%%%      Height_Modifier     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    
    def Height_Modifier(self,s,**kwargs):
        """ 
        Calculate Relative height growth for Spruce and pine trees 
        """
        sp= self.DERIVED_TREES[s].species
        
        if sp == "spruce": 
            a,b,c, K= 3.14,-1.16,-0.354, 500
        elif sp == "scots_pine": 
            a,b,c, K= 5.29,-1.9,0.525 , 100
            
        BAL = self.BAL(self.DERIVED_TREES[s],s)

        ba = self.DERIVED_TREES[s].ba
        if ba == 0.0:
            ba = 0.00000000000001
        
        CI4 = BAL/(BAL + K * ba)
                    
        ihrel1 = a * exp(b * (1 - CI4)** c) *  (1 - CI4)**(c)
        
        return ihrel1
    
                                                # %%%%%       Calculate stem volume     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

        
    def tree_volume(self,s, n_tree, aboveBark= True, **kwargs):
        """
        Calculate stem volume of single trees using Norwegian single tree volume functions for Norway Spruce, pine, Birch and other broadleaved trees

        Parameters
        ----------
        s : tree_id (string)
            Each tree object has a key and the values are the attributes of that tree. 
        aboveBark : TRUE or FALSE, optional
            To calculate volume inside Bark [m³]. The default is TRUE.
        **kwargs : TYPE
            dbh : Diameter in breast height in centimeter(cm)including bark
            height: Tree height in meter(m)

        Returns
        -------
        Volume for each tree in liters then changed to (m3/ha)

        """
        
        dbh = (self.DERIVED_TREES[s].dbh)/ 10 # centimeter
        height = (self.DERIVED_TREES[s].height)/ 10 # meter
        sp= self.DERIVED_TREES[s].species

        volsum = 0
        vol_spruce = 0
        vol_pine = 0
        vol_birch = 0
        vol_others = 0
        vol_ROS = 0
        vol_warm = 0

        if n_tree != 0:
            if sp == "spruce":
                
                if aboveBark:
                    a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4 = 0.52, 0.02403, 0.01463, -0.10983, 0.15195, -31.57, 0.0016, 0.0186, 0.63, -2.34, 3.2, 10.14, 0.0124, 0.03117, -0.36381, 0.28578           
                else:
                    a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4 = 0.38, 0.02524, 0.01269, -0.07726, 0.11671, -27.19, 0.0073, -0.0228, 0.5667, -1.98, 2.75, 8.66, 0.01218, 0.02976, -0.31373, 0.25452
                
                if dbh <= 10:
                    vol_spruce = (( a0 + a1 * dbh * dbh * height + a2 * dbh * height * height + a3 * height * height + a4 * dbh * height)/1000) *  n_tree
                elif dbh > 10 and dbh <= 13:
                    vol_spruce = ((b0 + b1 * dbh * height * height + b2 * height * height + b3 * dbh * height + b4 * height + b5 * dbh)/1000) *  n_tree
                else:
                    vol_spruce = ((c0 + c1 * dbh * dbh * height + c2 * dbh * height * height + c3 * height * height + c4 * dbh * height)/1000) *  n_tree
                
            elif sp == "scots_pine":  
                if aboveBark:
                    a0, a1, a2, b0, b1, b2, b3 = 2.9121, 0.039994, - 0.001091, 8.6524, 0.076844, 0.031573, 0
                else:
                    a0, a1, a2, b0, b1, b2, b3 = 2.2922, 0.040072, 0.00216, -3.5425, 0.128182, 0.028268, 0.008216
                    
                if dbh <= 11:
                    vol_pine = max(0, (((a0 + a1 * dbh * dbh * height + a2 * dbh * height * height)/1000) *  n_tree))
                else:
                    vol_pine = max(0, (((b0 + b1 * dbh * dbh + b2 * dbh * dbh * height + b3 * dbh * height + height)/1000) *  n_tree))
    
                    
            elif sp == "birch":
                
                B = 1.046 * dbh
                
                if aboveBark:
                    a0, a1, a2, a3, a4, a5 = -1.25409 , 0.12739, 0.03166, 0.0009752, -0.01226, -0.004214
                else:
                    a0, a1, a2, a3, a4, a5 = -1.48081 , 0.16945, 0.01834, 0.01018, -0.0451 , 0
                    
                vol_birch = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)/1000) *  n_tree))
    
    #        elif sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
            
            elif sp == "other_broadleaves":
                 
                B = 1.046 * dbh
                
                if aboveBark:
                    a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                    #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
                else:
                    a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
                #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
                vol_others = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))
            
            elif sp == "ROS":
                 
                B = 1.046 * dbh
                
                if aboveBark:
                    a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                    #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
                else:
                    a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
                #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
                vol_ROS = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))      
            
            elif sp == "warm":
                 
                B = 1.046 * dbh
                
                if aboveBark:
                    a0, a1, a2, a3, a4 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311
                    #a0, a1, a2, a3, a4, a5 = -1.25409, 0.12739, 0.03166, 0.0009752, - 0.01226, - 0.004214
                else:
                    a0, a1, a2, a3, a4, a5 = -1.86827 , 0.21461, 0.01283, 0.0138, -0.06311, 0
                #V = max(0, (a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height + a5 * dbh * dbh * B)) 
                vol_warm = max(0, (((a0 + a1 * dbh * dbh + a2 * dbh * dbh * height + a3 * dbh * height * height + a4 * height * height)/1000) *  n_tree))      
            
            volsum = vol_spruce + vol_pine + vol_birch + vol_others + vol_ROS + vol_warm
            Hardwood = vol_birch + vol_others + vol_ROS + vol_warm
            return volsum, vol_spruce, vol_pine, vol_birch , vol_others, vol_ROS , vol_warm, Hardwood
        
        else:
            volsum, vol_spruce, vol_pine, vol_birch , vol_others, vol_ROS , vol_warm = 0., 0. , 0., 0. , 0., 0. , 0.
            Hardwood = 0.
        
            return volsum, vol_spruce, vol_pine, vol_birch , vol_others, vol_ROS , vol_warm, Hardwood
    

                
    def volumeDoubleBark(self, s):#, Fitje1995 = False):
        """
        Functions for calculation of doublebark in milimeter

        Parameters
        ----------
        Fitje1995 : TYPE, optional
            Fitje1995 logical indicating to use the functions by Fitje 1995 rather than Brantseg 1967. The default is FALSE.

        Returns
        -------
        b doublebark i mm

        """
        dbh = self.DERIVED_TREES[s].dbh / 10
        height = self.DERIVED_TREES[s].height / 10
        sp= self.DERIVED_TREES[s].species
        
        if sp == "spruce" :     
            # Double bark i MM. Gran
            b = -0.34 + 0.831648 * dbh - 0.002832 * dbh * dbh - 0.010112 * height * height + 0.700203 * dbh * dbh / (height * height)
        elif sp == "scots_pine" :
            #Doublebark  Furu Fitje 1995
            # if(Fitje1995):
            #    b = 2.3 + 1.13 * dbh
            # else:
                # Double BARK I MM. Furu #Brantseg(1967) - page 702
            b = 2.9571 + 1.1499 * dbh - 0.7304 * dbh / height

## Check if calculating volume is same as other broadleaves               

#        elif sp in birch_species or sp in other_broadleaves_species or sp in ROS_species or sp in warm_species:
        else:
            #Doublebark BjÃ¸rk i mm
            b = 1.046 * dbh

        #Dobbelbark i mm        
        return b



                                                # %%%%%     fRegeneration    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    def fRegen(self, Regen_species, Regen_density,  year , period):

        """
        Returns
        -------
        None.

        """
        
#        years = 5
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if self.DERIVED_TREES[k].n_tree != 0]
        treefactordict = dict()
        
        for t in trees:
            treefactordict[t] = GrowthModel.DERIVED_TREES[t].tree_Factor 
        
        s = max(treefactordict.items(), key=operator.itemgetter(1))[0]
              
                
        if Regen_species == "Spruce":
            species = "spruce" 
            tree_sp = 1
#            b1, b2 = 2.2131, 0.3046
                
        elif Regen_species == "Pine":
            species = "scots_pine"
            tree_sp = 10
#            b1, b2 = 2.2845, 0.3318
                
        #Regen_species == "Birch":
        else: 
            species = "birch"
            tree_sp = 30
#            b1, b2 = 1.649, 0.373
                       
            
#        R_N = Regen_density/GrowthModel.DERIVED_TREES[s].tree_Factor
#        separated_num = math.modf(R_N) 
#        separated_num[1] # integer part
#        separated_num[0]*GrowthModel.DERIVED_TREES[s].tree_Factor # mod part
            
#        for i in range(1,R_N+1):    
        while True:
            id_= GrowthModel.tree_id_generation(GrowthModel.DERIVED_TREES[s],s)
            if id_ not in GrowthModel.DERIVED_TREES.keys():
                tree_id = id_
                break
                
#            tree_id = get_random_string(length=len(str(GrowthModel.DERIVED_TREES[s].tree_id)), allowed_chars='1234567890')
#            tree_id        = GrowthModel.DERIVED_TREES[s].tree_id + 0.01
        i = random.randint(40,200)
#        dbh            = 50 + i/100  # mm
        
        TF = GrowthModel.DERIVED_TREES[s].tree_Factor       
        
        dbh            = 50 + i/1000    # mm
        dbh_cm = dbh/10
        
        if GrowthModel.DERIVED_TREES[s].species == "spruce":
            b1, b2 =  1.877,  0.3276
            V_u1 , Cov_u1_u2, V_u2, R =  0.286,  -0.00858, 0.000942, 0.1905
            
            # Exp_Part1 = exp(-16.347 * ((dbh) ** -0.564))
            # height = (13 + (17142 * (GrowthModel.DERIVED_TREES[s].SI_m ** 0.2491) * (GrowthModel.DERIVED_TREES[s].LAT ** -1.0428) * (GrowthModel.DERIVED_TREES[s].altitude_m ** -0.0149)) * Exp_Part1)
 
        
        elif GrowthModel.DERIVED_TREES[s].species == "scots_pine":
            b1, b2 =  1.5007,  0.3747
            V_u1 , Cov_u1_u2, V_u2 , R = 0.4334, - 0.00729, 0.001891, 0.1784

            # Exp_Part1 = exp(-16.347 * ((dbh) ** -0.564))
            # height = (13 + (17125 * (GrowthModel.DERIVED_TREES[s].SI_m ** 0.4604) * (GrowthModel.DERIVED_TREES[s].LAT ** -1.328) ) * Exp_Part1) 

        # elif GrowthModel.DERIVED_TREES[s].species == "birch":
        #     Exp_Part1 = exp(-16.347 * ((dbh) ** -0.564))
        #     height = (13 + (1605.5 * (GrowthModel.DERIVED_TREES[s].SI_m ** 0.4606) * (GrowthModel.DERIVED_TREES[s].LAT ** -0.6737) * (GrowthModel.DERIVED_TREES[s].altitude_m **-0.022)) * Exp_Part1) 
                        
        else:
            b1, b2 =  1.1962, 0.4171
            V_u1 , Cov_u1_u2, V_u2 , R= 0.2481, - 0.01575, 0.002974, 0.1568

            # Exp_Part1 = exp(-14.833 * ((dbh) ** -0.5207))
            # height = (13 + (131104 * (GrowthModel.DERIVED_TREES[s].SI_m ** 0.3723) * (GrowthModel.DERIVED_TREES[s].LAT ** -1.6933) * (GrowthModel.DERIVED_TREES[s].altitude_m ** 0)) * Exp_Part1) 
        
        
        """ Compute 2x2 Variance-Covariance of two random effects
        
           [V[u1]    Cov(u1,u2)]
        D= 
           [Cov(u1,u2)    V[u2]]
        
        D is the determinants of Variance-Covariance matrix
        """
        a = np.array([[V_u1,Cov_u1_u2], [Cov_u1_u2,V_u2]]) 
        D = np.linalg.det(a)
        
        
        mu, sigma = 0, D
        u1 = np.random.normal(mu, sigma, 1)
        u2 = np.random.normal(mu, sigma, 1)
        epsilon = (mu, R, 1)
        
        SI_m = GrowthModel.DERIVED_TREES[s].SI_m
        
        # if SI_m >= 8:
        #     height         = ((13 +((dbh)/(b1+u1[0]+(b2+u2[0])*dbh))**3) + epsilon[0])/ 2 * 10  # convert to dm
        # else:
        #     height         = ((13 +((dbh)/(b1+u1[0]+(b2+u2[0])*dbh))**3) + epsilon[0])/ 3 * 10   # convert to dm
        height         = ((1.3 +((dbh_cm)/(b1+u1[0]+(b2+u2[0])*dbh_cm))**3) + epsilon[0]) * 10   # convert to dm
#        print(height)
        Diameter_Class = 5       
        DeadTrees      = 0 
        
        n_tree         = Regen_density 
        altitude_m     = GrowthModel.DERIVED_TREES[s].altitude_m
#            GrowthModel.GROWTH.append(volume)
        dead_trees     = DeadTrees
        
        species = GrowthModel.DERIVED_TREES[s].species
        VOLUME = GrowthModel.tree_volume_function(GrowthModel.DERIVED_TREES[s], dbh,height,n_tree, species, aboveBark= True)
        volsum = VOLUME[0]
        vol_spruce = VOLUME[1]
        vol_pine = VOLUME[2]
        vol_birch = VOLUME[3]
        vol_others = VOLUME[4]
        vol_ROS = VOLUME[5]
        vol_warm = VOLUME[6]
        
        ba = GrowthModel.update_ba(GrowthModel.DERIVED_TREES[s], dbh)
        
        CO_biomass_co2_tuple = GrowthModel.Regen_tree_biomass(GrowthModel.DERIVED_TREES[s],dbh,height,GrowthModel.DERIVED_TREES[s].species)
        BGB                  =  CO_biomass_co2_tuple[0]
        Tot_co2              =  CO_biomass_co2_tuple[1]
        Tot_biomass          =  CO_biomass_co2_tuple[2]
        Total_carbon         =  CO_biomass_co2_tuple[3]
        Biomass_BAR          =  CO_biomass_co2_tuple[7]
        Biomass_LGR          =  CO_biomass_co2_tuple[8]
        Biomass_RGE5         =  CO_biomass_co2_tuple[9]
        Biomass_RLT5         =  CO_biomass_co2_tuple[10]
        Tot_carbon_stems     =  CO_biomass_co2_tuple[11]
        Tot_carbon_roots     =  CO_biomass_co2_tuple[12]
        Tot_co2_stems        =  CO_biomass_co2_tuple[13]
        Tot_co2_roots        =  CO_biomass_co2_tuple[14]
        LitterProduction_tuple = GrowthModel.fLitter_Production_regeneration(GrowthModel.DERIVED_TREES[s],s,Biomass_BAR,Biomass_LGR,Biomass_RGE5,Biomass_RLT5 )
        unwl  = LitterProduction_tuple[0]
        ufwl  = LitterProduction_tuple[1]
        ucwl  = LitterProduction_tuple[2]
        
        # X and Y of tree coordinates: This is a random number and it will be used for visulaization purpose
        coord = np.random.random(2)
        coord   = coord[0] * _gridsize_x , coord[1] * _gridsize_y
        coord_x = coord[0]
        coord_y = coord[1]
                       
        for dom_spp in GrowthModel.Dominant_Height()[1]:
            Dom_species = dom_spp
        
        t_age = GrowthModel.tree_age(GrowthModel.DERIVED_TREES[s],s)
#        GrowthModel.GROWTH.append((tree_id,n_tree, GrowthModel.DERIVED_TREES[s].Period))
        attributes = dict(plot_id = GrowthModel.DERIVED_TREES[s].plot_id, tree_id = tree_id, tree_sp = tree_sp, year = year, dbh = dbh , height = height , diameter_class = Diameter_Class, 
                          tree_Factor = TF, n_tree = n_tree, SI_spp = GrowthModel.DERIVED_TREES[s].SI_spp,altitude_m =altitude_m , SI_m = SI_m, LAT = GrowthModel.DERIVED_TREES[s].LAT,
                          species = species, t_age = t_age, Period = period, yr_since_dead = 0 , Num_DeadTrees = dead_trees, Dom_species = Dom_species, BGB = BGB, Tot_co2 = Tot_co2, Tot_biomass = Tot_biomass, Total_carbon = Total_carbon, 
                          Tot_carbon_stems= Tot_carbon_stems,  Tot_carbon_roots = Tot_carbon_roots, Tot_co2_stems = Tot_co2_stems , Tot_co2_roots = Tot_co2_roots, vol_increment = 0. , dead_volume = 0., dead_co2 = 0., 
                          dead_biomass= 0., dead_C = 0.,  R_SPulp = GrowthModel.DERIVED_TREES[t].R_SPulp, R_PPulp = 0. , R_HPulp = 0., R_SSaw = 0. , R_PSaw = 0., R_HSaw = 0., Biomass_BAR = Biomass_BAR,
                          Biomass_LGR = Biomass_LGR, Biomass_RGE5 = Biomass_RGE5, Biomass_RLT5= Biomass_RLT5,unwl = unwl, ufwl= ufwl, ucwl = ucwl , temp = GrowthModel.DERIVED_TREES[s].temp,coord_x = coord_x, coord_y = coord_y,
                          volsum = volsum, vol_spruce = vol_spruce, vol_pine = vol_pine ,vol_birch = vol_birch, vol_others= vol_others, vol_ROS = vol_ROS, vol_warm = vol_warm, ba = ba, management = self.DERIVED_TREES[t].management)
              
        return   GrowthModel.TreeGenerator(new_cls_name = str(tree_id) , new_parameters= attributes)
    
    
                                                # %%%%%%  preparation for Ingrowth simulation   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    
    
    def BA_spruce(self):  
        """
        == BA_spruce        
        Calculate basal area for spruce species per hectare
        Return: plot basal area for spruce(m2ha-1)
        """
        SI_m=0
        sp=0
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]
        BA_S =  sum([(GrowthModel.DERIVED_TREES[k].ba * GrowthModel.DERIVED_TREES[k].n_tree) for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0 and GrowthModel.DERIVED_TREES[k].species == "spruce"])
        for t in trees:
            if GrowthModel.DERIVED_TREES[t].species == "spruce":
                SI_m = GrowthModel.DERIVED_TREES[t].SI_m
                sp = GrowthModel.DERIVED_TREES[t].species
                break
        
        return BA_S, SI_m, sp
    
    def BA_pine(self):  
        """
        == BA_pine  
        Calculate basal area for scot pine species per hectare
        Return: plot basal area for pine(m2ha-1)
        """

        SI_m=0
        sp=0
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]
        BA_P = sum([(GrowthModel.DERIVED_TREES[k].ba * GrowthModel.DERIVED_TREES[k].n_tree) for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0 and GrowthModel.DERIVED_TREES[k].species ==  "scots_pine"])
        for t in trees:
            if GrowthModel.DERIVED_TREES[t].species == "scots_pine":
                SI_m = GrowthModel.DERIVED_TREES[t].SI_m
                sp = GrowthModel.DERIVED_TREES[t].species
                break
            
        return BA_P, SI_m, sp
    
    def BA_birch(self):  
        """
        == BA_birch        
        Calculate basal area for spruce species per hectare
        Return: plot basal area for spruce(m2ha-1)
        """

        SI_m=0
        sp=0
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]
        BA_B = sum([(GrowthModel.DERIVED_TREES[k].ba * GrowthModel.DERIVED_TREES[k].n_tree) for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0 and GrowthModel.DERIVED_TREES[k].species ==  "birch"])
        for t in trees:
            if GrowthModel.DERIVED_TREES[t].species == "birch":
                SI_m = GrowthModel.DERIVED_TREES[t].SI_m
                sp = GrowthModel.DERIVED_TREES[t].species
            
        return BA_B, SI_m, sp
    
    def BA_OtherBroadleaves(self):  
        """
        == BA_others        
        Calculate basal area for spruce species per hectare
        Return: plot basal area for spruce(m2ha-1)
        """

        SI_m=0
        sp=0
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]
        BA_O_others = sum([(GrowthModel.DERIVED_TREES[k].ba * GrowthModel.DERIVED_TREES[k].n_tree) for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0 and GrowthModel.DERIVED_TREES[k].species ==  "other_broadleaves"])
        BA_O_ROS = sum([(GrowthModel.DERIVED_TREES[k].ba * GrowthModel.DERIVED_TREES[k].n_tree) for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0 and GrowthModel.DERIVED_TREES[k].species ==  "ROS"])
        BA_O_warm = sum([(GrowthModel.DERIVED_TREES[k].ba * GrowthModel.DERIVED_TREES[k].n_tree) for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0 and GrowthModel.DERIVED_TREES[k].species ==  "warm"])
        BA_O = BA_O_others + BA_O_ROS + BA_O_warm
        for t in trees:
            if GrowthModel.DERIVED_TREES[t].species == "other_broadleaves" or GrowthModel.DERIVED_TREES[t].species == "ROS" or GrowthModel.DERIVED_TREES[t].species == "warm":
                SI_m = GrowthModel.DERIVED_TREES[t].SI_m
                sp = GrowthModel.DERIVED_TREES[t].species
           
        return BA_O, SI_m, sp    
    
    
    def inGrowthModel_Bollandsas(self):
        
        BA_spruce_tuple = GrowthModel.BA_spruce(GrowthModel.DERIVED_TREES)
        BA_spruce       = BA_spruce_tuple[0]
        SI_spruce       = BA_spruce_tuple[1]
        spp_spruce      = BA_spruce_tuple[2]
        
        BA_pine_tuple   = GrowthModel.BA_pine(GrowthModel.DERIVED_TREES)
        BA_pine         = BA_pine_tuple[0]
        SI_pine         = BA_pine_tuple[1] 
        spp_pine        = BA_pine_tuple[2]
        
        BA_birch_tuple  = GrowthModel.BA_birch(GrowthModel.DERIVED_TREES)
        BA_birch        = BA_birch_tuple[0]
        SI_birch        = BA_birch_tuple[1]
        spp_birch       = BA_birch_tuple[2]
        
        BA_others_tuple = GrowthModel.BA_OtherBroadleaves(GrowthModel.DERIVED_TREES)
        BA_others       = BA_others_tuple[0]
        SI_others       = BA_others_tuple[1]
        spp_others      = BA_others_tuple[2]

      
        if (BA_spruce + BA_pine + BA_birch + BA_others) !=0:
            BA_stand = BA_spruce + BA_pine + BA_birch + BA_others
        else:
            BA_stand = 0.001      
        
        if  spp_spruce == "spruce": 
            Beta0,Beta1,Beta2,Beta3, alpha0, alpha1, alpha2, alpha3 = 43.142 , -0.157 , 0.368 , 0.051, -2.291, -0.018, 0.066, 0.019
            ingrowthN = (Beta0 * BA_stand ** (Beta1) * SI_spruce ** (Beta2) * (100 * (BA_spruce / BA_stand)) ** (Beta3)) * ((1 + exp(-(alpha0 + alpha1 * BA_stand + alpha2 * SI_spruce + alpha3 * (100 * (BA_spruce / BA_stand))))) ** -1)
#            ingrowthN = (Beta0 + BA_stand * (Beta1) + SI_spruce * (Beta2) + (100 * (BA_spruce / BA_stand)) * (Beta3)) * ((1 + exp(-(alpha0 + alpha1 * BA_stand + alpha2 * SI_spruce + alpha3 * (100 * (BA_spruce / BA_stand))))) ** -1)
#            GrowthModel.GROWTH.append((ingrowthN))
        elif spp_pine == "scots_pine":
            Beta0,Beta1,alpha0, alpha1, alpha3 = 67.152 , -0.076 , -3.552, - 0.062, 0.031
            ingrowthN = (Beta0 * BA_stand ** (Beta1)) * ((1 + exp(-(alpha0 + alpha1 * BA_stand + alpha3 * (100 * (BA_pine / BA_stand))))) ** -1)
#            ingrowthN = (Beta0 + BA_stand * (Beta1)) * ((1 + exp(-(alpha0 + alpha1 * BA_stand + alpha3 * (100 * (BA_pine / BA_stand))))) ** -1)
            
        elif spp_birch == "birch":
            Beta0,Beta1,Beta2,Beta3, alpha0, alpha1, alpha3 = 64.943 , -0.161 , 0.143 , 0.104, -0.904, -0.037, 0.016
            ingrowthN = (Beta0 * BA_stand ** (Beta1) * SI_birch ** (Beta2) * (100 * (BA_birch / BA_stand)) ** (Beta3)) * ((1 + exp(-(alpha0 + alpha1 * BA_stand + alpha3 * (100 * (BA_birch / BA_stand))))) ** -1)
#            ingrowthN = (Beta0 + BA_stand * (Beta1) + SI_birch * (Beta2) + (100 * (BA_birch / BA_stand)) * (Beta3)) * ((1 + exp(-(alpha0 + alpha1 * BA_stand + alpha3 * (100 * (BA_birch / BA_stand))))) ** -1) 
#        elif spp_others in other_broadleaves_species or spp_others in ROS_species or spp_others in warm_species:
        else:
            Beta0,Beta1,Beta2,Beta3, alpha0, alpha1, alpha2, alpha3 = 31.438 , -0.1695 , 0.442 , 0.193, -3.438, -0.029, 0.123, 0.048
            ingrowthN = (Beta0 * BA_stand ** (Beta1) * SI_others ** (Beta2) * (100 * (BA_others / BA_stand)) ** (Beta3)) * ((1 + exp(-(alpha0 + alpha1 * BA_stand + alpha2 * SI_others + alpha3 * (100 * (BA_others / BA_stand))))) ** -1)
#            ingrowthN = (Beta0 + BA_stand * (Beta1) + SI_others * (Beta2) + (100 * (BA_others / BA_stand)) * (Beta3)) * ((1 + exp(-(alpha0 + alpha1 * BA_stand + alpha2 * SI_others + alpha3 * (100 * (BA_others / BA_stand))))) ** -1)         
        
#        GrowthModel.GROWTH.append(int(ingrowthN))
        return int(ceil(ingrowthN))
    
                                                # %%%%%%     Main Ingrowth method        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    
    def tree_id_generation(self, s):
        
        tree_id = get_random_string(length=len(str(GrowthModel.DERIVED_TREES[s].tree_id)), allowed_chars='1234567890')

        return tree_id
    
    def ingrowth_species(self):
        #        years = 5
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]

        N_spruce = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "spruce" ])
        N_pine = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "scots_pine" ])
        N_birch = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "birch" ]) 
        N_others = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "other_broadleaves" ])
        N_ROS = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "ROS" ])
        N_warm =  sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "warm"])
        
        N_total = N_spruce + N_pine + N_birch + N_others + N_ROS + N_warm
        
        prop_spruce = N_spruce/N_total
        prop_pine  = N_pine/N_total
        prop_birch = N_birch/N_total
        prop_others = N_others/N_total
        prop_ROS = N_ROS/N_total
        prop_warm = N_warm/N_total

        
        s1, s10, s30, s50, s32, s40  = 0,0,0,0,0,0
        
        for t in trees:        
            if GrowthModel.DERIVED_TREES[t].species == "spruce":
                s1 = t
                
            elif GrowthModel.DERIVED_TREES[t].species == "scots_pine":
                s10 = t
                
            elif GrowthModel.DERIVED_TREES[t].species == "birch":
                s30 = t      

            elif GrowthModel.DERIVED_TREES[t].species == "other_broadleaves":  
                s50 = t
                

            elif GrowthModel.DERIVED_TREES[t].species == "ROS":
                s32 = t
                
            else:
                s40 = t
                
        tree_species = [(N_spruce,"spruce", prop_spruce, s1, 2.2131, 0.3046 ) , (N_pine, "scots_pine", prop_pine, s10, 2.2845, 0.3318) , 
                        (N_birch,"birch", prop_birch, s30, 1.649, 0.373) , (N_others,"other_broadleaves", prop_others, s50, 1.649, 0.373) 
                        , (N_ROS,"ROS", prop_ROS, s32,  1.649, 0.373) , (N_warm,"warm", prop_warm, s40, 1.649, 0.373   )]
        Dom_species = nlargest(6, tree_species)
           
        
        return Dom_species
    
    def ingrowth_implementation(self,ingrowthN, ingrow_trees, tree_id, i, s , year, period):
        
        """ 
        Returns
        -------
        Height, the total tree height (dm), dbh is the diameter at breast height (mm), 

        """

        TF = GrowthModel.DERIVED_TREES[s].tree_Factor       
        
        dbh            = 50 + i/1000    # mm
        dbh_cm = dbh/10
        if GrowthModel.DERIVED_TREES[s].species == "spruce":
            b1, b2 =  1.877,  0.3276
            V_u1 , Cov_u1_u2, V_u2, R =  0.286,  -0.00858, 0.000942, 0.1905

#            Exp_Part1 = exp(-16.347 * ((dbh) ** -0.564))
#            height = (13 + (17142 * (GrowthModel.DERIVED_TREES[s].SI_m ** 0.2491) * (GrowthModel.DERIVED_TREES[s].LAT ** -1.0428) * (GrowthModel.DERIVED_TREES[s].altitude_m ** -0.0149)) * Exp_Part1)
#        
        elif GrowthModel.DERIVED_TREES[s].species == "scots_pine":
            b1, b2 =  1.5007,  0.3747
            V_u1 , Cov_u1_u2, V_u2 , R = 0.4334, - 0.00729, 0.001891, 0.1784

#            Exp_Part1 = exp(-16.347 * ((dbh) ** -0.564))
#            height = (13 + (17125 * (GrowthModel.DERIVED_TREES[s].SI_m ** 0.4604) * (GrowthModel.DERIVED_TREES[s].LAT ** -1.328) ) * Exp_Part1) 

            
#        elif GrowthModel.DERIVED_TREES[s].species == "birch":
#            Exp_Part1 = exp(-16.347 * ((dbh) ** -0.564))
#            height = (13 + (1605.5 * (GrowthModel.DERIVED_TREES[s].SI_m ** 0.4606) * (GrowthModel.DERIVED_TREES[s].LAT ** -0.6737) * (GrowthModel.DERIVED_TREES[s].altitude_m **-0.022)) * Exp_Part1) 
#            
        else:
            b1, b2 =  1.1962, 0.4171
            V_u1 , Cov_u1_u2, V_u2 , R= 0.2481, - 0.01575, 0.002974, 0.1568

#            Exp_Part1 = exp(-14.833 * ((dbh) ** -0.5207))
#            height = (13 + (131104 * (GrowthModel.DERIVED_TREES[s].SI_m ** 0.3723) * (GrowthModel.DERIVED_TREES[s].LAT ** -1.6933) * (GrowthModel.DERIVED_TREES[s].altitude_m ** 0)) * Exp_Part1) 
#        
        """ Compute 2x2 Variance-Covariance of two random effects
        
           [V[u1]    Cov(u1,u2)]
        D= 
           [Cov(u1,u2)    V[u2]]
        
        D is the determinants of Variance-Covariance matrix
        """
        a = np.array([[V_u1,Cov_u1_u2], [Cov_u1_u2,V_u2]]) 
        D = np.linalg.det(a)
        
        
        mu, sigma = 0, D
        u1 = np.random.normal(mu, sigma, 1)
        u2 = np.random.normal(mu, sigma, 1)
        epsilon = (mu, R, 1)
        SI_m = GrowthModel.DERIVED_TREES[s].SI_m
        # if SI_m >= 8:
        #     height         = ((13 +((dbh)/(b1+u1[0]+(b2+u2[0])*dbh))**3) + epsilon[0])/ 2 * 10  # convert to dm
        # else:
        #     height         = ((13 +((dbh)/(b1+u1[0]+(b2+u2[0])*dbh))**3) + epsilon[0])/ 3 * 10   # convert to dm  
            
        height         = ((1.3 +((dbh_cm)/(b1+u1[0]+(b2+u2[0])*dbh_cm))**3) + epsilon[0]) * 10   # convert to dm        

        
        Diameter_Class = 5 
        DefectTrees      = 0 
        n_tree         =  TF * (ingrowthN / ingrow_trees)
        #height = height + 70
#        GrowthModel.GROWTH.append((height))
        dead_trees     = DefectTrees
        species = GrowthModel.DERIVED_TREES[s].species
        VOLUME = GrowthModel.tree_volume_function(GrowthModel.DERIVED_TREES[s], dbh,height,n_tree, species, aboveBark= True)
        volsum = VOLUME[0]
        vol_spruce = VOLUME[1]
        vol_pine = VOLUME[2]
        vol_birch = VOLUME[3]
        vol_others = VOLUME[4]
        vol_ROS = VOLUME[5]
        vol_warm = VOLUME[6]
        
        ba = GrowthModel.update_ba(GrowthModel.DERIVED_TREES[s], dbh)
        
        CO_biomass_co2_tuple = GrowthModel.Regen_tree_biomass(GrowthModel.DERIVED_TREES[s],dbh,height,GrowthModel.DERIVED_TREES[s].species)
        BGB                  =  CO_biomass_co2_tuple[0]
        Tot_co2              =  CO_biomass_co2_tuple[1]
        Tot_biomass          =  CO_biomass_co2_tuple[2]
        Total_carbon         =  CO_biomass_co2_tuple[3]
        Biomass_BAR          =  CO_biomass_co2_tuple[7]
        Biomass_LGR          =  CO_biomass_co2_tuple[8]
        Biomass_RGE5         =  CO_biomass_co2_tuple[9]
        Biomass_RLT5         =  CO_biomass_co2_tuple[10]
        Tot_carbon_stems     =  CO_biomass_co2_tuple[11]
        Tot_carbon_roots     =  CO_biomass_co2_tuple[12]
        Tot_co2_stems        =  CO_biomass_co2_tuple[13]
        Tot_co2_roots        =  CO_biomass_co2_tuple[14]
        
        
        LitterProduction_tuple = GrowthModel.fLitter_Production_regeneration(GrowthModel.DERIVED_TREES[s],s,Biomass_BAR,Biomass_LGR,Biomass_RGE5,Biomass_RLT5 )
        unwl  = LitterProduction_tuple[0]
        ufwl  = LitterProduction_tuple[1]
        ucwl  = LitterProduction_tuple[2]
        
        
        # X and Y of tree coordinates: This is a random number and it will be used for visulaization purpose
        coord = np.random.random(2)
        coord = coord[0] * _gridsize_x , coord[1] * _gridsize_y
        coord_x = coord[0]
        coord_y = coord[1]
        
        for dom_spp in GrowthModel.Dominant_Height()[1]:
            Dom_species = dom_spp
            break
#            GrowthModel.GROWTH.append((tree_id,n_tree))
        
        t_age = GrowthModel.tree_age(GrowthModel.DERIVED_TREES[s],s)
        
        attributes = dict(plot_id = GrowthModel.DERIVED_TREES[s].plot_id, tree_id = tree_id, tree_sp = GrowthModel.DERIVED_TREES[s].tree_sp, year = year, dbh = dbh , height = height , 
                          diameter_class = Diameter_Class, tree_Factor = TF, n_tree = n_tree, SI_spp = GrowthModel.DERIVED_TREES[s].SI_spp, altitude_m = GrowthModel.DERIVED_TREES[s].altitude_m, 
                          SI_m = SI_m , LAT = GrowthModel.DERIVED_TREES[s].LAT,species = species,  t_age = t_age, Period = period, yr_since_dead = 0 , Num_DeadTrees = dead_trees, 
                          Dom_species = Dom_species, BGB = BGB, Tot_co2 = Tot_co2, Tot_biomass = Tot_biomass, Total_carbon = Total_carbon,Tot_carbon_stems= Tot_carbon_stems,  Tot_carbon_roots = Tot_carbon_roots, 
                          Tot_co2_stems = Tot_co2_stems , Tot_co2_roots = Tot_co2_roots, vol_increment = 0., dead_volume = 0., dead_co2 = 0., dead_biomass= 0., dead_C = 0.,  R_SPulp = 0. , R_PPulp = 0. , R_HPulp = 0., 
                          R_SSaw = 0. , R_PSaw = 0., R_HSaw = 0., Biomass_BAR = Biomass_BAR, Biomass_LGR = Biomass_LGR, Biomass_RGE5 = Biomass_RGE5, Biomass_RLT5= Biomass_RLT5, unwl = unwl, ufwl = ufwl, ucwl = ucwl , 
                          temp = GrowthModel.DERIVED_TREES[s].temp, coord_x = coord_x, coord_y = coord_y, volsum = volsum, vol_spruce = vol_spruce,vol_pine =vol_pine , vol_birch = vol_birch, vol_others= vol_others, 
                          vol_ROS = vol_ROS, vol_warm = vol_warm, ba = ba, management = GrowthModel.DERIVED_TREES[s].management )
              
        return   GrowthModel.TreeGenerator(new_cls_name = str(tree_id) , new_parameters= attributes)
            
        
        
        
                                                # %%%%%%  Fertilization    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
            
    def Fertilization_Rosvall(self,PAI_,stand_age,ALTITUDE,SI,Latitude, year , period,mgt, **kwargs):
        """
        Calculate the fertilization impact according to Rosvall functions(1980).
        It reruns the fertilization response in m^3/ha then store it in  volume_increment object based on each tree
        
        CAI = volume at the end of year - volume at the beginning of the year
        """
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]

        N_spruce = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "spruce" ])
        N_pine = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "scots_pine" ])
        N_birch = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "birch" ]) 
        N_others = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "other_broadleaves" ])
        N_ROS = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "ROS" ])
        N_warm =  sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "warm"])
        
        
        all_trees = [k for k in GrowthModel.DERIVED_TREES.keys()]
        N_objects = len(trees)
               
        # This part will determine the the minority species for cutting
                
        N_stand = N_spruce + N_pine + N_birch + N_others + N_ROS + N_warm
        
        if N_stand == 0: N_stand = 0.01
        
        Pine_proportion = N_pine/N_stand
        
        self.PAI = PAI_
        self.stand_age = stand_age
        self.altitude = ALTITUDE
        self.SI = SI
        self.Latitude = Latitude
        AN = 150
        AN_SI = 150
               
        
        FertResponse = -4.368692 + (1.500548 * log(AN)) - (0.01208 * self.SI) - (0.000105 * (AN_SI)) - (0.018376 * (self.Latitude)) + 0.359554 * log(self.Latitude) - 0.000694 * (self.altitude) + 0.588503 * log(self.altitude) + \
        0.424878 * log( max(0.01, self.PAI)) - 0.003438 * self.stand_age + 0.412783 * log(self.stand_age) + 0.007016 * Pine_proportion
        
       
        if N_objects == 0: N_objects = 0.01
        f_response = FertResponse/N_objects
        
        mgt = mgt
        for t in all_trees:
            if (self.DERIVED_TREES[t].n_tree != 0):
                volume_increment = f_response
                #GrowthModel.GROWTH.append(volume_increment)
            else:
                 volume_increment = 0.          
            
            attributes = dict(plot_id = self.DERIVED_TREES[t].plot_id,tree_id = self.DERIVED_TREES[t].tree_id,tree_sp = self.DERIVED_TREES[t].tree_sp, year = year,  dbh = self.DERIVED_TREES[t].dbh , 
                              height = self.DERIVED_TREES[t].height, diameter_class = self.DERIVED_TREES[t].diameter_class, tree_Factor =self.DERIVED_TREES[t].tree_Factor, n_tree =self.DERIVED_TREES[t].n_tree,
                              SI_spp = self.DERIVED_TREES[t].SI_spp,altitude_m = self.DERIVED_TREES[t].altitude_m, SI_m = self.DERIVED_TREES[t].SI_m, LAT = self.DERIVED_TREES[t].LAT, species = self.DERIVED_TREES[t].species, 
                              t_age =self.DERIVED_TREES[t].t_age , Period = period, yr_since_dead = 0, Num_DeadTrees = self.DERIVED_TREES[t].Num_DeadTrees, Dom_species = self.DERIVED_TREES[t].Dom_species, BGB = self.DERIVED_TREES[t].BGB, 
                              Tot_co2 = self.DERIVED_TREES[t].Tot_co2, Total_carbon = self.DERIVED_TREES[t].Total_carbon, Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems , Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots, 
                              Tot_co2_stems = self.DERIVED_TREES[t].Tot_co2_stems, Tot_co2_roots = self.DERIVED_TREES[t].Tot_co2_roots, Tot_biomass = self.DERIVED_TREES[t].Tot_biomass, vol_increment = volume_increment, 
                              dead_volume = self.DERIVED_TREES[t].dead_volume, dead_co2 = self.DERIVED_TREES[t].dead_co2, dead_biomass= self.DERIVED_TREES[t].dead_biomass, dead_C = self.DERIVED_TREES[t].dead_C,  
                              R_SPulp = self.DERIVED_TREES[t].R_SPulp, R_PPulp = self.DERIVED_TREES[t].R_PPulp, R_HPulp = self.DERIVED_TREES[t].R_HPulp, R_SSaw =  self.DERIVED_TREES[t].R_SSaw , R_PSaw = self.DERIVED_TREES[t].R_PSaw, 
                              R_HSaw = self.DERIVED_TREES[t].R_HSaw, Biomass_BAR = self.DERIVED_TREES[t].Biomass_BAR, Biomass_LGR = self.DERIVED_TREES[t].Biomass_LGR, Biomass_RGE5 = self.DERIVED_TREES[t].Biomass_RGE5, 
                              Biomass_RLT5= self.DERIVED_TREES[t].Biomass_RLT5, unwl = self.DERIVED_TREES[t].unwl, ufwl = self.DERIVED_TREES[t].ufwl, ucwl = self.DERIVED_TREES[t].ucwl, temp = self.DERIVED_TREES[t].temp, 
                              coord_x = self.DERIVED_TREES[t].coord_x, coord_y = self.DERIVED_TREES[t].coord_y, volsum = self.DERIVED_TREES[t].volsum, vol_spruce = self.DERIVED_TREES[t].vol_spruce, vol_pine = self.DERIVED_TREES[t].vol_pine,
                              vol_birch = self.DERIVED_TREES[t].vol_birch, vol_others= self.DERIVED_TREES[t].vol_others , vol_ROS = self.DERIVED_TREES[t].vol_ROS, vol_warm = self.DERIVED_TREES[t].vol_warm, ba = self.DERIVED_TREES[t].ba , management = mgt)
        
            GrowthModel.TreeGenerator(new_cls_name = t , new_parameters= attributes)        
        
        

                                                # %%%%%       Calculate stem biomass for regeneration     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        


    def Regen_tree_biomass(self,D,H,SP):
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
        sp: tree species (Norway spruce, Scots Pine, Birch)
        
        Returns
        -------
        A data with the dry weight biomass (kg) / Carbon/ CO2 for the specified components.
        
        Components
        ----------
        STV: biomass of stem wood            # spruce or pine or birch
        STB: biomass of stem bark            # bark
        ---> stem biomass = STV + STB
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
        dbh = D/10  # convert to centimeter
        height = H / 10 # convert to meter
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
            
            Biomass_RGE5 = Compute_biomass_ab(8,13.3703,-6.3851)
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
            
        Tot_biomass = Biomass_ST  + Biomass_LGR + Biomass_DGR + Biomass_STU + Biomass_BGB #Biomass_BAR + Biomass_RGE5 + Biomass_RLT5
        Total_carbon = Tot_biomass * Carbon_conversion_factor
        Tot_co2 = Total_carbon * CO2_Fraction
        
        
        Tot_biomass_dead   = Biomass_ST
        Total_carbon_dead  = Tot_biomass_dead * Carbon_conversion_factor
        Tot_co2_dead       = Total_carbon_dead * CO2_Fraction
        
        Tot_carbon_stems = Biomass_ST*Carbon_conversion_factor
        Tot_carbon_roots = (Biomass_LGR + Biomass_DGR + Biomass_STU + Biomass_BAR + Biomass_RGE5 + Biomass_RLT5)*Carbon_conversion_factor
        Tot_co2_stems = Tot_carbon_stems * CO2_Fraction
        Tot_co2_roots = Tot_carbon_roots * CO2_Fraction
            

        
        return Biomass_BGB, Tot_co2, Tot_biomass, Total_carbon, Tot_co2_dead, Tot_biomass_dead, Total_carbon_dead, Biomass_BAR, Biomass_LGR, Biomass_RGE5, Biomass_RLT5, Tot_carbon_stems, Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots

                                                # %%%%%%     fDeadtrees    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

 
    def fDeadtrees(self):
        """
        This function calculates the amount of carbon, co2 and biomass of deadtrees (Natural)
        """
 
        Dead_trees =  [k for k in GrowthModel.DeadTrees.keys() if self.DERIVED_TREES[k].DeadTrees != 0]                          
        Tot_co2=0.0
        Tot_biomass=0.0
        Total_carbon=0.0
        for stem in Dead_trees:
            Tot_co2      +=  GrowthModel.DERIVED_TREES[stem].dead_co2/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
            Tot_biomass  +=  GrowthModel.DERIVED_TREES[stem].dead_biomass/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
            Total_carbon +=  GrowthModel.DERIVED_TREES[stem].dead_C/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
            
#        GrowthModel.GROWTH.append((BGB,Tot_co2,Tot_biomass,Total_carbon))
        
        return Tot_co2, Tot_biomass, Total_carbon
    
                                                # %%%%%%     fTimberProducts    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%     
    
    def fTimberProducts(self, s, DBH , HEIGHT):
        
        """
        Product                   Specifications
        ------------------------------------------
        Sawtimber                    >=30.5 cm dbh
        Pulpwood                     >=15.1 cm dbh
        ------------------------------------------
        DBH (diameter breast height) is in mm, while H (Height) is in dm. 
        """

        R_SPulp = 0.
        R_SSaw  = 0.
        R_PPulp = 0.
        R_PSaw  = 0.
        R_HPulp = 0.
        R_HSaw  = 0.   
         
        if GrowthModel.DERIVED_TREES[s].species == "spruce":
            if GrowthModel.DERIVED_TREES[s].n_tree != 0:
                # Pulpwood and saw share spruce 
                R_SPulp = (5411.076 + 2.4982*DBH - 570.0585*log(DBH) + 2.4086*HEIGHT - 581.6202*log(HEIGHT) - 0.003287*DBH*HEIGHT)/10000
                
                if R_SPulp < 0:
                    R_SPulp = 0
                elif R_SPulp > 1:
                    R_SPulp = 1
                    
                R_SSaw = 1 - R_SPulp

                
        elif GrowthModel.DERIVED_TREES[s].species == "scots_pine":
            if GrowthModel.DERIVED_TREES[s].n_tree != 0:
                # Pulp wood and saw timber share pine 
                R_PPulp =  (5639.345 + 2.6042*DBH - 680.7972*log(DBH) + 2.4537*HEIGHT - 525.9713*log(HEIGHT) - 0.002645*DBH*HEIGHT)/10000
                
                if R_PPulp < 0:
                    R_PPulp = 0
                elif R_PPulp > 1:
                    R_PPulp = 1
                    
                R_PSaw = 1 - R_PPulp


        #GrowthModel.DERIVED_TREES[s].species == "birch"
        else:
            
            if GrowthModel.DERIVED_TREES[s].n_tree != 0:
                 # Pulp wood and saw timber share broadleaf
                R_HPulp = 5.0022 + 8.1463 - 2.417 * log(HEIGHT)
                
                if R_HPulp < 0:
                    R_HPulp = 0
                elif R_HPulp > 1:
                    R_HPulp = 1
                    
                R_HSaw  = 1 - R_HPulp
        
 
#        GrowthModel.GROWTH.append((R_SPulp, R_SSaw , R_PPulp, R_PSaw, R_HPulp, R_HSaw))
          
        return R_SPulp, R_SSaw , R_PPulp, R_PSaw, R_HPulp, R_HSaw


                                                # %%%%%     fLitter_Production for small AND large trees    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
    
    def fLitter_Production_regeneration(self,s,Biomass_BAR,Biomass_LGR,Biomass_RGE5,Biomass_RLT5):
        
        """
        This function will calculate the litter input to Yasso Model by using turnover rates for small trees (recruitment)
        =================================================================================================
        return:
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
        Latitude = self.DERIVED_TREES[s].LAT
        
        if GrowthModel.DERIVED_TREES[s].species == "spruce":
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
            
        elif GrowthModel.DERIVED_TREES[s].species == "scots_pine":
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
            
        unwl   = Foilage1 * (Biomass_BAR) +  Fine_root1 * (Biomass_RLT5)
        ufwl   = Branches1 * (Biomass_LGR) + Roots1 * (Biomass_RGE5)
        ucwl   = 0
        
        return unwl, ufwl, ucwl
        
                                                # %%%%%     fLitter_Production for large trees    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
        
    def fLitter_Production(self, s):
        """
        This function will calculate the litter input to Yasso Model by using turnover rates for large trees
        =================================================================================================
        return: 
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
        Latitude = self.DERIVED_TREES[s].LAT
        
        if GrowthModel.DERIVED_TREES[s].species == "spruce":
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
            
        elif GrowthModel.DERIVED_TREES[s].species == "scots_pine":
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
             
        unwl   = Foilage1  * (self.DERIVED_TREES[s].Biomass_BAR) +  Fine_root1 * (self.DERIVED_TREES[s].Biomass_RLT5)
        ufwl   = Branches1 * (self.DERIVED_TREES[s].Biomass_LGR) +  Roots1 * (self.DERIVED_TREES[s].Biomass_RGE5)
        ucwl   = 0
#        self.GROWTH.append((unwl,ufwl))
        return unwl, ufwl, ucwl 
    
    
                                                # %%%%%%     fSoilCarbon    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
    
    def fSoilCarbon(self):
        """
        Calculate the amount of soil organic carbon (Ton/m2)
        
        """
        
        trees    = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]
        Deadtrees = [k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0] 
        

        soilCarbon = 0.
        # carbon of litter production from living trees
        for each in trees:
            
            unwl = self.DERIVED_TREES[each].unwl/1000 * self.DERIVED_TREES[each].n_tree
            ufwl = self.DERIVED_TREES[each].ufwl/1000 * self.DERIVED_TREES[each].n_tree
            ucwl = self.DERIVED_TREES[each].ucwl/1000 * self.DERIVED_TREES[each].n_tree
            
            for i in range(5):
                soilCarbon += YassoModel.decomp_one_timestep(unwl/5, ufwl/5, ucwl/5, self.DERIVED_TREES[each].temp )[1]
        # carbon of litter production from dead wood branches trees
        for rest in  Deadtrees:
            
            unwld = self.DERIVED_TREES[rest].unwl/1000 *  GrowthModel.DERIVED_TREES[rest].Num_DeadTrees
            ufwld = self.DERIVED_TREES[rest].ufwl/1000 *  GrowthModel.DERIVED_TREES[rest].Num_DeadTrees
            ucwld = self.DERIVED_TREES[rest].ucwl/1000 *  GrowthModel.DERIVED_TREES[rest].Num_DeadTrees
            
            for i in range(5):
                soilCarbon += YassoModel.decomp_one_timestep(unwld/5, ufwld/5, ucwld/5, GrowthModel.DERIVED_TREES[rest].temp)[1]
            
        return soilCarbon
      
                                                    # %%%%%     fMeanAnnualTemp    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

    # def fMeanAnnualTemp(self):
                
    #     trees    = [k for k in GrowthModel.DERIVED_TREES.keys()] 
    #     Deadtrees = [k for k in GrowthModel.DeadTrees.keys()] 

    #     for each in trees:           
    #         MeanAirTemperature = self.MeanAnnualTemp(self.DERIVED_TREES[each].stationID , self.DERIVED_TREES[each].referencetime)
    #         break
    #     for rest in  Deadtrees:
    #         #self.GROWTH.append(self.DERIVED_TREES[each].stationID)
    #         MeanAirTemperatureDead = self.MeanAnnualTemp(self.DERIVED_TREES[rest].stationID , self.DERIVED_TREES[rest].referencetime)
    #         break
        
    #     return MeanAirTemperature, MeanAirTemperatureDead     
    
    
                                                    # %%%%%    Mean Annual Temperature    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
    
    def MeanAnnualTemp(self, stationID , referencetime ):
        
        
        # Insert your own client ID here
        client_id = 'fa62bbb4-5814-46a7-8429-01a650d6de77'
        
        # Define endpoint and parameters
        endpoint = 'https://frost.met.no/observations/v0.jsonld'
        parameters = {
            'sources': stationID , #'SN90450'
            'elements': 'mean(air_temperature P1D)', 'timeoffsets': 'PT0H' , "timeresolutions": "P1D", 'referencetime': referencetime } # '2016'}
        
        # Issue an HTTP GET request
        r = requests.get(endpoint, parameters, auth=(client_id,''))
        # Extract JSON data
        json = r.json()
        
        # Check if the request worked, print out any errors
        if r.status_code == 200:
            data = json['data']
        #    print('Data retrieved from frost.met.no!')
        else:
            print('Error! Returned status code %s' % r.status_code)
            # print('Message: %s' % json['error']['message'])
            # print('Reason: %s' % json['error']['reason'])
                
        # This will return a Dataframe with all of the observations in a table format
        df = pd.DataFrame()

        for i in range(len(data)):
            row = pd.DataFrame(data[i]['observations'])
            row['referenceTime'] = data[i]['referenceTime']
            row['sourceId'] = data[i]['sourceId']
            df = df.append(row)
        
        df = df.reset_index()
        
        # These additional columns will be kept
        columns = ['sourceId','referenceTime','elementId','value','unit','timeOffset']
        df2 = df[columns].copy()
        
        # Convert the time value to something Python understands
        df2['referenceTime'] = pd.to_datetime(df2['referenceTime'])
        mean_Annual_Temp = float(np.mean(df2['value']))

        return mean_Annual_Temp
    
     
                                                    # %%%%%    Models for the remaining fraction of mass of deadwoods    %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
    
    def deadwood_decay_mass(self): #, M_spti_1, M_spti_2, M_spti_3, M_spti_4, M_spti_5,M_spti_6
        
        """
        according to Mäkinen et al. (2006), this function calculate the remaining fraction of mass of f Scots pine, Norway spruce, and birch
        
        inputs
        ------
        dbh_spt0 = Stem diameter at the time of tree death (cm)
        y_spti = time since tree death (yr)
        m_spt0 =  mass at the time of tree death
        m_spti = mass since tree death 
        delta_1spt = random parameter based on sd(gamma_1spt) and mean
        SD(gamma_1spt) = standard devation of the random parameter
        d1,d2,d3,d4,d5,d6,d7 = mass parameters
        
    
        Returns
        -------
        remaining fraction of mass of deadwoods = M_spti/M_spt0
    
        """
               
        Deadtrees = [k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0]
#        print(Deadtrees)
        
        Deadtrees_spruce = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].species == "spruce"])) 
        Deadtrees_pine = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].species == "scots_pine"])) 
        Deadtrees_birch = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].species == "birch"])) 
        Deadtrees_other = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].species == "other_broadleaves"]))
        Deadtrees_ROS = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].species == "ROS"]))
        Deadtrees_warm = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].species == "warm"]))       

         
        num_trees = len(Deadtrees)
        
        if Deadtrees_spruce == 0: Deadtrees_spruce = 0.0001
        
        if Deadtrees_pine == 0: Deadtrees_pine = 0.0001
        
        if Deadtrees_birch == 0: Deadtrees_birch = 0.0001
        
        if Deadtrees_other == 0: Deadtrees_other = 0.0001
        
        if Deadtrees_ROS == 0: Deadtrees_ROS = 0.0001
        
        if Deadtrees_warm == 0: Deadtrees_warm = 0.0001
        
        
        d1, d2, d3, d4, d5, d6, d7 = -1.849, -2.017, -1.893, 0.064, 0.054, 0.149, -0.017      

        SD_delta_1spt, SD_delta_2spt, SD_delta_3spt =   0.850, 1.116, 1.007

        mu = 0        
        
        delta_2spt = np.random.normal(mu, SD_delta_2spt, 1) #spruce
        delta_1spt = np.random.normal(mu, SD_delta_1spt, 1) #pine
        delta_3spt = np.random.normal(mu, SD_delta_3spt, 1) #birch
        delta_4spt = np.random.normal(mu, SD_delta_3spt, 1) #other
        delta_5spt = np.random.normal(mu, SD_delta_3spt, 1) #ROS           
        delta_6spt = np.random.normal(mu, SD_delta_3spt, 1) #warm   

        
        T_Mass_spruce, T_Mass_pine, T_Mass_birch, T_Mass_others, T_Mass_ROS, T_Mass_warm = 0.,0.,0.,0.,0.,0.

        y_spti_spruce,y_spti_pine, y_spti_birch, y_spti_others, y_spti_ROS, y_spti_warm = 0., 0., 0., 0., 0., 0.

        dbh_spt0_spruce, dbh_spt0_pine,dbh_spt0_birch,dbh_spt0_other, dbh_spt0_ROS,dbh_spt0_warm = 0., 0., 0., 0., 0., 0.

        Total_V_remain_spruce,Total_V_remain_pine,Total_V_remain_birch, Total_V_remain_others, Total_V_remain_ROS, Total_V_remain_warm   = 0., 0., 0., 0., 0., 0.
        
        T_Decomposition_spruce, T_Decomposition_pine,T_Decomposition_birch, T_Decomposition_others, T_Decomposition_ROS, T_Decomposition_warm  = 0., 0., 0., 0., 0., 0.
        
        
        for stem in Deadtrees:
            if self.DERIVED_TREES[stem].species == "spruce":
                Mass_spruce    =  GrowthModel.DERIVED_TREES[stem].dead_biomass/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
                T_Mass_spruce += Mass_spruce
                y_spti_spruce = GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']*5
                dbh_spt0_spruce = GrowthModel.DERIVED_TREES[stem].dbh/10
                if Deadtrees_spruce >= 0.1:
                    remain_fraction_spruce = exp(-1 * exp(d2 + (d5 * y_spti_spruce) + (d7 * dbh_spt0_spruce) + delta_2spt ))
                else:
                    remain_fraction_spruce = 0.   
                    
                M_remain_spruce         =  Mass_spruce * remain_fraction_spruce
                Decomposition_spruce    =  Mass_spruce - M_remain_spruce
                Total_V_remain_spruce  += M_remain_spruce
                T_Decomposition_spruce += Decomposition_spruce
            
            elif self.DERIVED_TREES[stem].species == "scots_pine":
                Mass_pine      =  GrowthModel.DERIVED_TREES[stem].dead_biomass/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
                T_Mass_pine   += Mass_pine
                y_spti_pine    = GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']*5
                dbh_spt0_pine  = GrowthModel.DERIVED_TREES[stem].dbh/10
                if Deadtrees_pine >= 0.1:
                    remain_fraction_pine   = exp(-1 * exp(d1 + (d4 * y_spti_pine)   + (d7 * dbh_spt0_pine) + delta_1spt ))
                else:
                    remain_fraction_pine = 0.
                    
                M_remain_pine         =  Mass_pine * remain_fraction_pine
                Decomposition_pine    =  Mass_pine - M_remain_pine
                Total_V_remain_pine  += M_remain_pine
                T_Decomposition_pine += Decomposition_pine
                
            elif self.DERIVED_TREES[stem].species == "birch":
                Mass_birch     =  GrowthModel.DERIVED_TREES[stem].dead_biomass/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
                T_Mass_birch  += Mass_birch
                y_spti_birch   = GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']*5
                dbh_spt0_birch = GrowthModel.DERIVED_TREES[stem].dbh/10
                if Deadtrees_birch >= 0.1:
                    remain_fraction_birch  = exp(-1 * exp(d3 + (d6 * y_spti_birch)  + (d7 * dbh_spt0_birch) + delta_3spt))
                else:
                    remain_fraction_birch = 0.
                    
                M_remain_birch         =  Mass_birch * remain_fraction_birch
                Decomposition_birch    =  Mass_birch - M_remain_birch
                Total_V_remain_birch  += M_remain_birch
                T_Decomposition_birch += Decomposition_birch
            
            elif self.DERIVED_TREES[stem].species == "other_broadleaves":
                Mass_others    =  GrowthModel.DERIVED_TREES[stem].dead_biomass/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
                T_Mass_others +=  Mass_others
                y_spti_others  = GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']*5
                dbh_spt0_other = GrowthModel.DERIVED_TREES[stem].dbh/10  
                if Deadtrees_other >= 0.1:
                    remain_fraction_others = exp(-1 * exp(d3 + (d6 * y_spti_others) + (d7 * dbh_spt0_other) + delta_4spt))
                else:
                    remain_fraction_others = 0.
                    
                M_remain_others         =  Mass_others * remain_fraction_others
                Decomposition_others    =  Mass_others - M_remain_others
                Total_V_remain_others  += M_remain_others
                T_Decomposition_others += Decomposition_others
            
            elif self.DERIVED_TREES[stem].species == "ROS":
                Mass_ROS     =  GrowthModel.DERIVED_TREES[stem].dead_biomass/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
                T_Mass_ROS  += Mass_ROS
                y_spti_ROS   = GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']*5
                dbh_spt0_ROS = GrowthModel.DERIVED_TREES[stem].dbh/10   
                if Deadtrees_ROS >= 0.1:
                    remain_fraction_ROS = exp(-1 * exp(d3 + (d6 * y_spti_ROS) + (d7 * dbh_spt0_ROS) + delta_5spt))
                else:
                    remain_fraction_ROS = 0. 
                    
                M_remain_ROS         =  Mass_ROS * remain_fraction_ROS
                Decomposition_ROS    =  Mass_ROS - M_remain_ROS
                Total_V_remain_ROS  += M_remain_ROS
                T_Decomposition_ROS += Decomposition_ROS
            
            else:
                Mass_warm     = GrowthModel.DERIVED_TREES[stem].dead_biomass/1000 *  GrowthModel.DERIVED_TREES[stem].Num_DeadTrees
                T_Mass_warm  += Mass_warm
                y_spti_warm   = GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']*5
                dbh_spt0_warm = GrowthModel.DERIVED_TREES[stem].dbh/10
                if Deadtrees_warm >= 0.1:
                    remain_fraction_warm = exp(-1 * exp(d3 + (d6 * y_spti_warm) + (d7 * dbh_spt0_warm) + delta_5spt))
                else:
                    remain_fraction_warm = 0. 
                
                M_remain_warm        =  Mass_warm * remain_fraction_warm
                Decomposition_warm    =  Mass_warm - M_remain_warm
                Total_V_remain_warm  += M_remain_warm
                T_Decomposition_warm += Decomposition_warm
            
        
            
#        #GrowthModel.GROWTH.append((remain_fraction_spruce,y_spti_spruce)) 
#        M_spt0_spruce = Mass_spruce #+ M_spti_1
#        M_spt0_pine = Mass_pine #+ M_spti_2
#        M_spt0_birch = Mass_birch #+ M_spti_3
#        M_spt0_others = Mass_others #+ M_spti_4
#        M_spt0_ROS = Mass_ROS #+ M_spti_5
#        M_spt0_warm = Mass_warm #+ M_spti_6
#        
#        M_spti_spruce = M_spt0_spruce * remain_fraction_spruce
#        Decomposition_spruce = M_spt0_spruce - M_spti_spruce
#
#        
#        M_spti_pine = M_spt0_pine * remain_fraction_pine
#        Decomposition_pine = M_spt0_pine - M_spti_pine
#
#        
#        M_spti_birch = M_spt0_birch * remain_fraction_birch
#        Decomposition_birch = M_spt0_birch - M_spti_birch
#
#        
#        M_spti_others = M_spt0_others * remain_fraction_others
#        Decomposition_other = M_spt0_others - M_spti_others
#
#        M_spti_ROS = M_spt0_ROS * remain_fraction_ROS
#        Decomposition_ROS = M_spt0_ROS - M_spti_ROS
#
#        M_spti_warm = M_spt0_warm * remain_fraction_warm
#        Decomposition_warm = M_spt0_warm - M_spti_warm

        
        Decomposition=  T_Decomposition_spruce + T_Decomposition_pine +T_Decomposition_birch + T_Decomposition_others + T_Decomposition_ROS + T_Decomposition_warm 

        Dead_wood_carbon =  0.5  * Decomposition
        Dead_wood_co2 = 3.67 * Dead_wood_carbon
        
        
        
        return  Dead_wood_co2, Dead_wood_carbon #M_spti_spruce, M_spti_pine, M_spti_birch, M_spti_others, M_spti_ROS, M_spti_warm, 
    
    
    
                                                # %%%%%     Biodiversity indicator - amount of deadwood  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

    def deadwood_decay_vol(self, volume_deadwood_p0): 
        
        """
        according to Mäkinen et al. (2006) table 8, this function calculate the remaining fraction of stem volume
        
        inputs
        ------
        dbh_spt0 = Stem diameter at the time of tree death (cm)
        y_spti = time since tree death (yr)
        v_spt0 =  stem volume at the time of tree death
        v_spti = stem volume since tree death 
        gamma_1spt = random parameter based on sd(gamma_1spt) and mean
        SD(gamma_1spt) = standard devation of the random parameter
        c1,c2,c3,c4,c5,c6,c7 = volume parameters
        
    
        Returns
        -------
        remaining fraction of stem volume = V_spti/V_spt0

        ###================================================================================================================================================================
        ### Biodiversity Indicator                           definition                       100 points                  50 points          0 points
        ###================================================================================================================================================================                
        ### amount of deadwood                          |   Volume (m3/ha)   |                > 20 m3/ha           <= 20 and >=5 m3/ha         < 5
        ###----------------------------------------------------------------------------------------------------------------------------------------------------------------    
        """
        
        
        Deadtrees = [k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0] 
        
#        GrowthModel.GROWTH.append((Deadtrees))
                
        Deadtrees_spruce = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0 and GrowthModel.DERIVED_TREES[k].species == "spruce"])) 
        Deadtrees_pine = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0 and GrowthModel.DERIVED_TREES[k].species == "scots_pine"])) 
        Deadtrees_birch = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0 and GrowthModel.DERIVED_TREES[k].species == "birch"]))
        Deadtrees_other = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0 and GrowthModel.DERIVED_TREES[k].species == "other_broadleaves"]))
        Deadtrees_ROS = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0 and GrowthModel.DERIVED_TREES[k].species == "ROS"]))
        Deadtrees_warm = len(set([k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0 and GrowthModel.DERIVED_TREES[k].species == "warm"]))       
#        keysP1 = [k for k in GrowthModel.DeadTrees.keys() if GrowthModel.DERIVED_TREES[k].Num_DeadTrees != 0]
#        valuesP1= [GrowthModel.DERIVED_TREES[k].DeadList['yr_since_dead'] for k in keysP1]
#        keysP0 = keysP0
#        valuesP0 = valuesP0
#        y_spti = dict(zip(keysP1, valuesP1))
#        y_spt0 = dict(zip(keysP0, valuesP0))


        
        num_trees = len(Deadtrees)
        
        if Deadtrees_spruce == 0: Deadtrees_spruce = 0.0001
        
        if Deadtrees_pine == 0: Deadtrees_pine = 0.0001
        
        if Deadtrees_birch == 0: Deadtrees_birch = 0.0001
        
        if Deadtrees_other == 0: Deadtrees_other = 0.0001
        
        if Deadtrees_ROS == 0: Deadtrees_ROS = 0.0001
        
        if Deadtrees_warm == 0: Deadtrees_warm = 0.0001 
        
        
        c1, c2, c3, c4, c5, c6, c7 = -2.653, -2.948, -3.324, 0.055, 0.059, 0.135, -0.030      

        SD_gamma_1spt, SD_gamma_2spt, SD_gamma_3spt =   1.191, 0.912,  1.091

        mu = 0        
        
        gamma_2spt = np.random.normal(mu, SD_gamma_2spt, 1) #spruce
        gamma_1spt = np.random.normal(mu, SD_gamma_1spt, 1) #pine
        gamma_3spt = np.random.normal(mu, SD_gamma_3spt, 1) #birch
        gamma_4spt = np.random.normal(mu, SD_gamma_3spt, 1) #other
        gamma_5spt = np.random.normal(mu, SD_gamma_3spt, 1) #ROS
        gamma_6spt = np.random.normal(mu, SD_gamma_3spt, 1) #warm

        


        T_volume_spruce, T_volume_pine, T_volume_birch, T_volume_others, T_volume_ROS, T_volume_warm   = 0., 0., 0., 0., 0., 0.        
        
        Total_V_remain_spruce, Total_V_remain_pine, Total_V_remain_birch, Total_V_remain_others, Total_V_remain_ROS, Total_V_remain_warm  = 0., 0., 0., 0., 0., 0.
        
        T_Decomposition_spruce, T_Decomposition_pine, T_Decomposition_birch, T_Decomposition_others, T_Decomposition_ROS, T_Decomposition_warm = 0., 0., 0., 0., 0., 0.
        
        dbh_spt0_spruce, dbh_spt0_pine, dbh_spt0_birch,dbh_spt0_other, dbh_spt0_ROS, dbh_spt0_warm = 0., 0., 0., 0., 0., 0.
        
        for stem in Deadtrees:
#            GrowthModel.GROWTH.append((stem, GrowthModel.DERIVED_TREES[stem].Period, GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']))
            if self.DERIVED_TREES[stem].species == "spruce":
                volume_spruce    =  GrowthModel.DERIVED_TREES[stem].dead_volume 
                T_volume_spruce += volume_spruce
                y_spti_spruce    =  (GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead'] * 5)               
                dbh_spt0_spruce  = GrowthModel.DERIVED_TREES[stem].DeadList['dbh']/10
                if Deadtrees_spruce >= 0.001:
                    remain_fraction_spruce = exp(-1 * exp(c2 + (c5 * y_spti_spruce) + (c7 * dbh_spt0_spruce) + gamma_2spt ))
                else:
                    remain_fraction_spruce = 0.                
                V_remain_spruce         =  volume_spruce * remain_fraction_spruce
                Decomposition_spruce    =  volume_spruce - V_remain_spruce
                Total_V_remain_spruce  += V_remain_spruce
                T_Decomposition_spruce += Decomposition_spruce
                
            elif self.DERIVED_TREES[stem].species == "scots_pine":
                volume_pine    =  GrowthModel.DERIVED_TREES[stem].dead_volume 
                T_volume_pine += volume_pine
                y_spti_pine    =  (GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead'] * 5)
                dbh_spt0_pine  = GrowthModel.DERIVED_TREES[stem].DeadList['dbh']/10
                if Deadtrees_pine >= 0.001:
                    remain_fraction_pine   = exp(-1 * exp(c1 + (c4 * y_spti_pine)   + (c7 * dbh_spt0_pine) + gamma_1spt ))
                else:
                    remain_fraction_pine = 0.
                V_remain_pine         =  volume_pine * remain_fraction_pine
                Decomposition_pine    =  volume_pine - V_remain_pine
                Total_V_remain_pine  += V_remain_pine
                T_Decomposition_pine += Decomposition_pine                                       
                
            elif self.DERIVED_TREES[stem].species == "birch":
                volume_birch    =  GrowthModel.DERIVED_TREES[stem].dead_volume 
                T_volume_birch += volume_birch
                y_spti_birch    =  (GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead'] * 5)
                dbh_spt0_birch  = GrowthModel.DERIVED_TREES[stem].DeadList['dbh']/10 
                
                if Deadtrees_birch >= 0.001:
                    remain_fraction_birch  = exp(-1 * exp(c3 + (c6 * y_spti_birch)  + (c7 * dbh_spt0_birch) + gamma_3spt))
                else:
                    remain_fraction_birch = 0.
                V_remain_birch         =  volume_birch * remain_fraction_birch
                Decomposition_birch    =  volume_birch - V_remain_birch
                Total_V_remain_birch  += V_remain_birch
                T_Decomposition_birch += Decomposition_birch                     
                    
                    
            elif self.DERIVED_TREES[stem].species == "other_broadleaves":
                volume_others    =  GrowthModel.DERIVED_TREES[stem].dead_volume 
                T_volume_others += volume_others
                y_spti_others    =  (GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']* 5) 
                dbh_spt0_other   = GrowthModel.DERIVED_TREES[stem].DeadList['dbh']/10            
                if Deadtrees_other >= 0.001:
                    remain_fraction_others = exp(-1 * exp(c3 + (c6 * y_spti_others) + (c7 * dbh_spt0_other) + gamma_4spt))
                else:
                    remain_fraction_others = 0.
                V_remain_others         =  volume_others * remain_fraction_others
                Decomposition_others    =  volume_others - V_remain_others
                Total_V_remain_others  += V_remain_others
                T_Decomposition_others += Decomposition_others
                
                
            elif self.DERIVED_TREES[stem].species == "ROS":
                volume_ROS    =  GrowthModel.DERIVED_TREES[stem].dead_volume 
                T_volume_ROS += volume_ROS
                y_spti_ROS    =  (GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead'] * 5)
                dbh_spt0_ROS  = GrowthModel.DERIVED_TREES[stem].DeadList['dbh']/10  
                if Deadtrees_ROS >= 0.001:
                    remain_fraction_ROS = exp(-1 * exp(c3 + (c6 * y_spti_ROS) + (c7 * dbh_spt0_ROS) + gamma_5spt))
                else:
                    remain_fraction_ROS = 0.   
                V_remain_ROS         =  volume_ROS * remain_fraction_ROS
                Decomposition_ROS    =  volume_ROS - V_remain_ROS
                Total_V_remain_ROS  += V_remain_ROS
                T_Decomposition_ROS += Decomposition_ROS                   
            else:
                volume_warm    =  GrowthModel.DERIVED_TREES[stem].dead_volume 
                T_volume_warm += volume_warm
                y_spti_warm    = (GrowthModel.DERIVED_TREES[stem].DeadList['yr_since_dead']* 5) 
                dbh_spt0_warm  = GrowthModel.DERIVED_TREES[stem].DeadList['dbh']/10                           
                if Deadtrees_warm >= 0.001:
                    remain_fraction_warm = exp(-1 * exp(c3 + (c6 * y_spti_warm) + (c7 * dbh_spt0_warm) + gamma_6spt))
                else:
                    remain_fraction_warm = 0.              
                V_remain_warm         =  volume_warm * remain_fraction_warm
                Decomposition_warm    =  volume_warm - V_remain_warm
                Total_V_remain_warm  += V_remain_warm
                T_Decomposition_warm += Decomposition_warm             
       
#        V_spti_spruce = Total_V_remain_spruce - V_spt0_spruce
#        V_spti_pine = Total_V_remain_pine - V_spt0_pine
#        V_spti_birch = Total_V_remain_birch - V_spt0_birch
#        V_spti_others = Total_V_remain_others - V_spt0_others
#        V_spti_ROS = Total_V_remain_ROS - V_spt0_ROS
#        V_spti_warm = Total_V_remain_warm - V_spt0_warm


        volume_deadwood_p0 = volume_deadwood_p0
        Decomposition= T_Decomposition_spruce + T_Decomposition_pine + T_Decomposition_birch + T_Decomposition_others + T_Decomposition_ROS + T_Decomposition_warm
        volume_deadwood = Total_V_remain_spruce + Total_V_remain_pine + Total_V_remain_birch + Total_V_remain_others + Total_V_remain_ROS + Total_V_remain_warm
#        volume_deadwood = V_spti_spruce + V_spti_pine + V_spti_birch + V_spti_others + V_spti_ROS + V_spti_warm
        
#        volume_deadwood_NoDecay = T_volume_spruce + T_volume_pine + T_volume_birch + T_volume_others + T_volume_ROS + T_volume_warm
#        GrowthModel.GROWTH.append((volume_spruce,  ))
#        points = 0
#        if volume_deadwood >= 20:
#            points = 100
#        elif volume_deadwood < 20 and volume_deadwood >= 5:
#            points = 50
#        else:
#            points = 0
        points = 0
        
        if volume_deadwood - volume_deadwood_p0 >= 5:
            points = 1
        else:
            points = 0           
#        GrowthModel.GROWTH.append((points))    
        return  volume_deadwood, Decomposition, points, volume_deadwood #, volume_deadwood_NoDecay , valuesP1, keysP1


                                                # %%%%%    Biodiversity indicator - Species richness  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
    
    def species_richness(self):
        """
        species richness is the number of species present in the plot in each period
        
        ### Biodiversity Indicator                     definition                          100 points                  50 points             0 points
        ###================================================================================================================================================================        
        ### Species richness             | # of species present in that plot   |         all species(>=4)               2- 3                  <= 1
        ###----------------------------------------------------------------------------------------------------------------------------------------------------------------        
        """      
        
        value_spruce = len(set([k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "spruce" and GrowthModel.DERIVED_TREES[k].n_tree != 0]))
        value_pine = len(set([k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "scots_pine" and GrowthModel.DERIVED_TREES[k].n_tree != 0]))
        value_birch = len(set([k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "birch" and GrowthModel.DERIVED_TREES[k].n_tree != 0]))
        value_other = len(set([k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "other_broadleaves" if GrowthModel.DERIVED_TREES[k].n_tree != 0]))
        value_ROS = len(set([k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "ROS" and GrowthModel.DERIVED_TREES[k].n_tree != 0]))
        value_warm = len(set([k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "warm" and GrowthModel.DERIVED_TREES[k].n_tree != 0]))
##****************************************         
        if value_spruce != 0:
            u_value_spruce =1
        else:
            u_value_spruce=0
##****************************************        
        if value_pine != 0:
            u_value_pine =1
        else:
            u_value_pine=0
##****************************************             
        if value_birch != 0:
            u_value_birch =1
        else:
            u_value_birch=0
##**************************************** 
        if value_other != 0:
            u_value_other =1
        else:
            u_value_other=0
##**************************************** 
        if value_ROS != 0:
            u_value_ROS =1
        else:
            u_value_ROS=0
##**************************************** 
        if value_warm != 0:
            u_value_warm =1
        else:
            u_value_warm=0
##****************************************        
        u_value =  u_value_spruce + u_value_pine + u_value_birch + u_value_other + u_value_ROS + u_value_warm

#        points = 0
#        if u_value >= 4:
#            points = 100
#        elif u_value <4 and u_value >= 2:
#            points = 50
#        else:
#            points = 0
        points = 0
        if u_value >= 3:
            points = 1
        else:
            points = 0
        return u_value, points


                                                # %%%%%    Biodiversity indicator - Species diversity (Shannon Index)  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

    def calc_alpha(self):
        """
        Calculating the plot biodiversity(species diversity) using the Shannon Index
        alpha = diversity index, alpha = 0 means only one species present in that plot
        S = # of species
        ln = natural log
        p[i] = proportion of individuals in the sample belonging to the ith species
        n[i] = # of individuals of species i
        N_stand = total number of individuals of all species in plot j
        p[i] = n[i]/N
        
        ###================================================================================================================================================================
        ### Biodiversity Indicator                                         definition                      100 points                  50 points             0 points
        ###================================================================================================================================================================               
        ### Species diversity (Shannon Index) alpha      | combines species richness and evenness|            >= 1                  <1 and >= 0.5            < 0.5        
        ###----------------------------------------------------------------------------------------------------------------------------------------------------------------        
        """
        trees= set([k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0])
        
        
        N_spruce, N_pine, N_birch, N_others, N_ROS, N_warm = 0.0000000001,0.0000000001,0.0000000001,0.0000000001,0.0000000001,0.0000000001
        
        for k in trees:
        
            if GrowthModel.DERIVED_TREES[k].species == "spruce":
                N_spruce += GrowthModel.DERIVED_TREES[k].n_tree                   
            elif GrowthModel.DERIVED_TREES[k].species == "scots_pine":
                N_pine +=GrowthModel.DERIVED_TREES[k].n_tree
            elif GrowthModel.DERIVED_TREES[k].species == "birch":
                N_birch +=GrowthModel.DERIVED_TREES[k].n_tree
            elif GrowthModel.DERIVED_TREES[k].species == "other_broadleaves":
                N_others +=GrowthModel.DERIVED_TREES[k].n_tree
            elif GrowthModel.DERIVED_TREES[k].species == "ROS":
                N_ROS +=GrowthModel.DERIVED_TREES[k].n_tree               
            else:
                N_warm +=GrowthModel.DERIVED_TREES[k].n_tree
                
        
        counts = [N_spruce, N_pine, N_birch, N_others, N_ROS, N_warm ]      
        fracs = np.array(counts, dtype=float)
        
        fracs = fracs/sum(fracs)

        alpha = -1*sum(fracs*np.log(fracs))
        
#        points = 0
#        if alpha >= 1:
#            points = 100
#        elif alpha < 1 and alpha >= 0.5:
#            points = 50
#        else:
#            points = 0
        points = 0
        if alpha >= 0.7:
            points = 1
        else:
            points = 0
            
        return alpha, points
            


                                                # %%%%%%     Biodiversity indicator - amount of large decidous trees other than birch  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

    def large_decidous_vol(self):
        """
        The volume of decidous trees larger than 40 cm (400 mm) dbh (m3/ha)
        
        
        ###================================================================================================================================================================
        ### Biodiversity Indicator                                definition                      100 points                  50 points             0 points
        ###================================================================================================================================================================               
        ### amount of large decidous trees other than birch  |   Volume (m3/ha)   |              > 10 m3/ha           <= 10 and >=5 m3/ha             < 5
        ###----------------------------------------------------------------------------------------------------------------------------------------------------------------
        """
        
#        trees= [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]
    
            
        vol_others = sum([(self.DERIVED_TREES[k].vol_others + self.DERIVED_TREES[k].vol_increment) for k in set(self.DERIVED_TREES.keys()) if (self.DERIVED_TREES[k].n_tree != 0) and self.DERIVED_TREES[k].dbh > 400])
        vol_ROS = sum([(self.DERIVED_TREES[k].vol_ROS + self.DERIVED_TREES[k].vol_increment) for k in set(self.DERIVED_TREES.keys()) if (self.DERIVED_TREES[k].n_tree != 0) and self.DERIVED_TREES[k].dbh > 400])
        vol_warm =  sum([(self.DERIVED_TREES[k].vol_warm + self.DERIVED_TREES[k].vol_increment) for k in set(self.DERIVED_TREES.keys()) if (self.DERIVED_TREES[k].n_tree != 0) and self.DERIVED_TREES[k].dbh > 400])      
        
        
        decidous_vol = [vol_others, vol_ROS , vol_warm]
        vol = np.array(decidous_vol, dtype=float)
        vol = sum(vol)
        points = 0
        
#
#        if vol > 10:
#            points = 100
#        elif vol <= 10 and vol > 5:
#            points = 50
#        else:
#            points = 0
        
        if vol > 7:
            points = 1
        else:
            points = 0
        
        return vol, points
                    
                    
                                                # %%%%%     Biodiversity indicator - number of large trees  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

    def large_trees(self):
        """
        The number of large trees in the plot (N/ha)

            ###================================================================================================================================================================
            ### Biodiversity Indicator            definition                 100 points                  50 points             0 points
            ###================================================================================================================================================================                
            ### number of large trees            |   N/ha  |               tree > 50cm dbh             tree > 40cm dbh       not present
            ###----------------------------------------------------------------------------------------------------------------------------------------------------------------  
        
        """
        #trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]

        Large_spruce_50 = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "spruce" and GrowthModel.DERIVED_TREES[k].dbh > 500)])
        Large_pine_50 = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "scots_pine" and GrowthModel.DERIVED_TREES[k].dbh > 500)])
        Large_birch_50 = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "birch" and GrowthModel.DERIVED_TREES[k].dbh > 500)]) 
        Large_decidous_50_others = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "other_broadleaves" and GrowthModel.DERIVED_TREES[k].dbh > 500)])
        Large_decidous_50_ROS = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "ROS" and GrowthModel.DERIVED_TREES[k].dbh > 500)])
        Large_decidous_50_warm =  sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "warm" and GrowthModel.DERIVED_TREES[k].dbh > 500)])
        Large_spruce_40 = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "spruce" and GrowthModel.DERIVED_TREES[k].dbh > 400)])
        Large_pine_40 = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "scots_pine"  and GrowthModel.DERIVED_TREES[k].dbh > 400)])
        Large_birch_40 = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "birch"  and GrowthModel.DERIVED_TREES[k].dbh > 400)]) 
        Large_decidous_40_others = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "other_broadleaves"  and GrowthModel.DERIVED_TREES[k].dbh > 400)])
        Large_decidous_40_ROS = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "ROS" and  GrowthModel.DERIVED_TREES[k].dbh > 400)])
        Large_decidous_40_warm = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in set(GrowthModel.DERIVED_TREES.keys()) if (GrowthModel.DERIVED_TREES[k].species == "warm" and GrowthModel.DERIVED_TREES[k].dbh > 400)])
        
        
        Large_decidous_50  = Large_decidous_50_others + Large_decidous_50_ROS + Large_decidous_50_warm
        Large_decidous_40  = Large_decidous_40_others + Large_decidous_40_ROS + Large_decidous_40_warm
#        GrowthModel.GROWTH.append((Large_spruce_50 + Large_pine_50 + Large_birch_50 + Large_decidous_50))
        large_greaterthan50 = Large_spruce_50 + Large_pine_50 + Large_birch_50 + Large_decidous_50
        large_greaterthan40 = Large_spruce_40 + Large_pine_40 + Large_birch_40 + Large_decidous_40
        
#        GrowthModel.GROWTH.append((large_greaterthan50,large_greaterthan40))
#        points = 0
#        if large_greaterthan50 > 50:
#            points = 100
#        elif large_greaterthan40 > 40 :
#            points = 50
#        else:
#            points = 0
        points = 0
        if large_greaterthan50 > 45:
            points = 1

        else:
            points = 0
            
        return large_greaterthan50, points

                                                    # %%%%%     Biodiversity indicator - mature broadleaf-rich forest  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
#todo
                                                    
                                                    
                                                    
                                                               
                                                    # %%%%%     fR_Thinn     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        
    
    def fR_Thinn(self, R_BGB,R_co2,R_biomass, R_carbon,R_carbon_stems, R_carbon_roots, R_co2_stems,R_co2_roots, 
                 G_b, R_G, Removed_trees,R_vol_tot,R_vol_spruce,R_vol_pine,R_vol_birch,R_vol_others,R_vol_ros,
                 R_vol_warm, mic_tp, year, period, mgt, **kwargs):
        """
        This function removes the objects (minority species) which have met the conditions for thining 
        
        """
        Remove_BGB          =  R_BGB
        Remove_co2          =  R_co2
        Remove_biomass      =  R_biomass 
        Remove_carbon       =  R_carbon
        Remove_carbon_stems =  R_carbon_stems
        Remove_carbon_roots =  R_carbon_roots 
        Remove_co2_stems    =  R_co2_stems
        Remove_co2_roots    =  R_co2_roots
        
        N_removed    = Removed_trees
        R_BA         = R_G
        R_vol_tot    = R_vol_tot
        R_vol_spruce = R_vol_spruce
        R_vol_pine   = R_vol_pine
        R_vol_birch  = R_vol_birch
        R_vol_others = R_vol_others
        R_vol_ros    = R_vol_ros 
        R_vol_warm   = R_vol_warm
        R_v_others     = R_vol_birch + R_vol_others + R_vol_ros + R_vol_warm
        G_before = G_b
        mic_t = mic_tp
              
        trees_spruce, trees_pine, trees_others =[],[],[]
        trees_dict = collections.defaultdict(dict)
        R_SPulp = collections.defaultdict(dict)
        R_PPulp = collections.defaultdict(dict)
        R_HPulp = collections.defaultdict(dict)
        R_SSaw  = collections.defaultdict(dict)
        R_PSaw  = collections.defaultdict(dict)
        R_HSaw  = collections.defaultdict(dict)
        
        volsum  = collections.defaultdict(dict)
        vol_spruce  = collections.defaultdict(dict)
        vol_pine  = collections.defaultdict(dict)
        vol_birch  = collections.defaultdict(dict)
        vol_others  = collections.defaultdict(dict)
        vol_ROS  = collections.defaultdict(dict)
        vol_warm  = collections.defaultdict(dict)
        
        BGB                = collections.defaultdict(dict) 
        Tot_co2            = collections.defaultdict(dict)
        Tot_biomass        = collections.defaultdict(dict)
        Total_carbon       = collections.defaultdict(dict)
        Tot_carbon_stems   = collections.defaultdict(dict)
        Tot_carbon_roots   = collections.defaultdict(dict)
        Tot_co2_stems      = collections.defaultdict(dict)
        Tot_co2_roots       = collections.defaultdict(dict)

        
        ba = collections.defaultdict(dict)
        
        # This part will determine the the minority species for cutting
        V_sum = sum([(self.DERIVED_TREES[k].volsum + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys()])
        V_spruce = sum([(self.DERIVED_TREES[k].vol_spruce + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_pine = sum([(self.DERIVED_TREES[k].vol_pine + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_birch = sum([(self.DERIVED_TREES[k].vol_birch + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])  
        V_other = sum([(self.DERIVED_TREES[k].vol_others + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_ROS = sum([(self.DERIVED_TREES[k].vol_ROS + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_warm =  sum([(self.DERIVED_TREES[k].vol_warm + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])        
        
        V_others = V_birch + V_other + V_ROS + V_warm
        
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]

        # N_spruce = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "spruce" ])
        # N_pine = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "scots_pine" ])
        # N_birch = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "birch" ]) 
        # N_other = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "other_broadleaves" ])
        # N_ROS = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "ROS" ])
        # N_warm =  sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "warm"])        
        
        # N_others = N_birch + N_other + N_ROS + N_warm
        
        Scenario_spruce_thin       = ["pine_only", "others_some", "others_pine", "pine_others", "others_spruce", "pine_spruce", "spruce_only", "pine_others_spruce"]
        Scenario_pine_thin         = ["spruce_only", "others_some", "others_spruce", "spruce_others", "spruce_others_pine", "others_pine", "spruce_pine", "pine_only"]
        
        
        for k in trees:
            if GrowthModel.DERIVED_TREES[k].species == "spruce" and (GrowthModel.DERIVED_TREES[k].n_tree != 0):
                trees_spruce.append(k)
                
            elif GrowthModel.DERIVED_TREES[k].species == "scots_pine" and (GrowthModel.DERIVED_TREES[k].n_tree != 0):
                trees_pine.append(k)
                
            elif (GrowthModel.DERIVED_TREES[k].species == "birch" or GrowthModel.DERIVED_TREES[k].species == "other_broadleaves" or GrowthModel.DERIVED_TREES[k].species == "ROS" or GrowthModel.DERIVED_TREES[k].species == "warm") and (GrowthModel.DERIVED_TREES[k].n_tree != 0):
                trees_others.append(k)
      
        # this part difines the Minor species type for thinning
        Minor_species = ""
        if (mic_t == "High_spruce") or (mic_t == "Medium_spruce"):
                
            if R_vol_tot <= (V_pine + V_others): # case1
                
                if (R_vol_tot <= V_pine) and (R_vol_tot < V_others) and (V_pine < V_others):
                    Minor_species = Scenario_spruce_thin[0]
                elif (R_vol_tot < V_pine) and (R_vol_tot >= V_others) and (V_pine > V_others):
                    Minor_species = Scenario_spruce_thin[1]
                
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_others) and (V_pine >= V_others):
                    Minor_species = Scenario_spruce_thin[2]
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_others) and (V_others > V_pine ):
                    Minor_species = Scenario_spruce_thin[3]                  
                    
                elif (R_vol_tot < V_pine) and (R_vol_tot > V_others):
                     Minor_species = Scenario_spruce_thin[2]
                elif (R_vol_tot > V_pine) and (R_vol_tot < V_others):
                     Minor_species = Scenario_spruce_thin[3] 
                elif (R_vol_tot == V_pine) and (R_vol_tot > V_others):
                    Minor_species = Scenario_spruce_thin[0]
                elif (R_vol_tot == V_others) and (R_vol_tot >= V_pine):
                    Minor_species = Scenario_spruce_thin[1]
                elif (R_vol_tot > V_others) and (R_vol_tot != V_pine) and (V_others <= V_pine):
                    Minor_species = Scenario_spruce_thin[2]
                elif (R_vol_tot > V_pine) and (V_pine <= V_others):
                    Minor_species = Scenario_spruce_thin[3]
                    
                    
            elif R_vol_tot > (V_pine + V_others) and V_pine != 0 and V_others != 0: # case2
                Minor_species = Scenario_spruce_thin[7]   #"pine_others_spruce" 
                
            elif R_vol_tot > (V_pine + V_others) and V_pine == 0 and V_others != 0: # case3
                Minor_species = Scenario_spruce_thin[4] # "others_spruce" 
                
            elif R_vol_tot > (V_pine + V_others) and V_pine != 0 and V_others == 0: # case4
                Minor_species = Scenario_spruce_thin[5] #"pine_spruce" 
            
            elif R_vol_tot > (V_pine + V_others) and V_pine == 0 and V_others == 0: # case5
                Minor_species = Scenario_spruce_thin[6] # "spruce_only"
        
        elif (mic_t == "High_pine") or (mic_t == "Medium_pine"):
            
            if R_vol_tot <= (V_spruce + V_others): # case1
                
                if (R_vol_tot <= V_spruce) and (R_vol_tot < V_others) and (V_spruce < V_others):
                    Minor_species = Scenario_pine_thin[0]
                elif (R_vol_tot < V_spruce) and (R_vol_tot <= V_others) and (V_spruce > V_others):
                    Minor_species = Scenario_pine_thin[1]
                
                elif (R_vol_tot > V_spruce) and (R_vol_tot > V_others) and (V_spruce >= V_others):
                    Minor_species = Scenario_pine_thin[2]
                elif (R_vol_tot > V_spruce) and (R_vol_tot > V_others) and (V_others > V_spruce ):
                    Minor_species = Scenario_pine_thin[3]                   
                    
                elif (R_vol_tot < V_spruce) and (R_vol_tot > V_others):
                     Minor_species = Scenario_pine_thin[2]
                elif (R_vol_tot > V_spruce) and (R_vol_tot < V_others):
                     Minor_species = Scenario_pine_thin[3]
                elif (R_vol_tot == V_spruce) and (R_vol_tot > V_others):
                    Minor_species = Scenario_pine_thin[0]
                elif (R_vol_tot == V_others) and (R_vol_tot >= V_spruce):
                    Minor_species = Scenario_pine_thin[1]
                elif (R_vol_tot > V_others) and (V_others <= V_spruce):
                    Minor_species = Scenario_pine_thin[2]
                elif (R_vol_tot > V_spruce) and (V_spruce <= V_others):
                    Minor_species = Scenario_pine_thin[3]
                    
                    
            elif R_vol_tot > (V_spruce + V_others) and V_spruce != 0 and V_others != 0: # case2
                Minor_species = Scenario_pine_thin[4]  #"spruce_others_pine"
                
            elif R_vol_tot > (V_spruce + V_others) and V_spruce == 0 and V_others != 0: # case3
                Minor_species = Scenario_pine_thin[5] # "others_pine" 
                
            elif R_vol_tot > (V_spruce + V_others) and V_spruce != 0 and V_others == 0: # case4
                Minor_species = Scenario_pine_thin[6] # "spruce_pine" 
            
            elif R_vol_tot > (V_spruce + V_others) and V_spruce == 0 and V_others == 0: # case5
                Minor_species = Scenario_pine_thin[7] # "pine_only"
            
                
          
        # this list will be used for updating the objects
        spruce_toDelete = trees_spruce.copy()
        others_toDelete = trees_others.copy()
        others1_toDelete = trees_others.copy()
        spruce_toDelete2 = trees_spruce.copy()
        spruce_toDelete8 = trees_spruce.copy()
        others_toDelete2 = trees_others.copy()
        pine_toDelete2 = trees_pine.copy()
        pine_toDelete4 = trees_pine.copy()
        others_toDelete3 = trees_others.copy()
        pine_toDelete3 = trees_pine.copy()
        others_toDelete4 = trees_others.copy()
        others_toDelete5 = trees_others.copy()
        
        
        if (mic_t == "High_pine") or (mic_t == "Medium_pine"):
            #(mic_t == "High_pine") or (mic_t == "Medium_pine")
            if (Minor_species ==  "spruce_others"):                 
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and (len(spruce_toDelete) != 0):
                        Results_1stCompound_spruce1_thin = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems,
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                     N_removed, G_before)
                        N_removed                  = Results_1stCompound_spruce1_thin[0]
                        R_vol_spruce               = Results_1stCompound_spruce1_thin[1]
                        trees_dict[t]              = Results_1stCompound_spruce1_thin[2]
                        volsum[t]                  = Results_1stCompound_spruce1_thin[3]
                        vol_spruce[t]              = Results_1stCompound_spruce1_thin[4]
                        vol_pine[t]                = Results_1stCompound_spruce1_thin[5]
                        vol_birch[t]               = Results_1stCompound_spruce1_thin[6]
                        vol_others[t]              = Results_1stCompound_spruce1_thin[7]
                        vol_ROS[t]                 = Results_1stCompound_spruce1_thin[8]
                        vol_warm[t]                = Results_1stCompound_spruce1_thin[9]
                        R_SPulp[t]                 = Results_1stCompound_spruce1_thin[10]
                        R_SSaw[t]                  = Results_1stCompound_spruce1_thin[11]
                        R_HSaw[t]                  = Results_1stCompound_spruce1_thin[12]
                        R_HPulp[t]                 = Results_1stCompound_spruce1_thin[13]
                        R_PSaw[t]                  = Results_1stCompound_spruce1_thin[14]
                        R_PPulp[t]                 = Results_1stCompound_spruce1_thin[15]
                        G_before                   = Results_1stCompound_spruce1_thin[16]
                        R_BA                       = Results_1stCompound_spruce1_thin[17]
                        ba[t]                      = Results_1stCompound_spruce1_thin[18]
                        BGB[t]                     = Results_1stCompound_spruce1_thin[19]
                        Tot_co2[t]                 = Results_1stCompound_spruce1_thin[20]
                        Tot_biomass[t]             = Results_1stCompound_spruce1_thin[21]
                        Total_carbon[t]            = Results_1stCompound_spruce1_thin[22]
                        Tot_carbon_stems[t]        = Results_1stCompound_spruce1_thin[23]
                        Tot_carbon_roots[t]        = Results_1stCompound_spruce1_thin[24]
                        Tot_co2_stems[t]           = Results_1stCompound_spruce1_thin[25]
                        Tot_co2_roots[t]           = Results_1stCompound_spruce1_thin[26]
                        spruce_toDelete.remove(str(t))
                        
                            
                for tree in trees:
                    t= tree
                    if (t in trees_others)  and len(spruce_toDelete) == 0:
                        Results_2ndCompound_others1_thin = self.SecondCompound_Others(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                      Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA,R_vol_birch,
                                                                                      R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        
                        N_removed                   = Results_2ndCompound_others1_thin[0]
                        R_vol_birch                 = Results_2ndCompound_others1_thin[1]
                        R_vol_others                = Results_2ndCompound_others1_thin[2]
                        R_vol_ros                   = Results_2ndCompound_others1_thin[3]
                        R_vol_warm                  = Results_2ndCompound_others1_thin[4]
                        trees_dict[t]               = Results_2ndCompound_others1_thin[5]
                        volsum[t]                   = Results_2ndCompound_others1_thin[6]
                        vol_spruce[t]               = Results_2ndCompound_others1_thin[7]
                        vol_pine[t]                 = Results_2ndCompound_others1_thin[8]
                        vol_birch[t]                = Results_2ndCompound_others1_thin[9]
                        vol_others[t]               = Results_2ndCompound_others1_thin[10]
                        vol_ROS[t]                  = Results_2ndCompound_others1_thin[11]
                        vol_warm[t]                 = Results_2ndCompound_others1_thin[12]
                        R_SPulp[t]                  = Results_2ndCompound_others1_thin[13]
                        R_SSaw[t]                   = Results_2ndCompound_others1_thin[14]
                        R_HSaw[t]                   = Results_2ndCompound_others1_thin[15]
                        R_HPulp[t]                  = Results_2ndCompound_others1_thin[16]
                        R_PSaw[t]                   = Results_2ndCompound_others1_thin[17]
                        R_PPulp[t]                  = Results_2ndCompound_others1_thin[18]
                        G_before                    = Results_2ndCompound_others1_thin[19]
                        R_BA                        = Results_2ndCompound_others1_thin[20]
                        ba[t]                       = Results_2ndCompound_others1_thin[21]
                        BGB[t]                      = Results_2ndCompound_others1_thin[19]
                        Tot_co2[t]                  = Results_2ndCompound_others1_thin[20]
                        Tot_biomass[t]              = Results_2ndCompound_others1_thin[21]
                        Total_carbon[t]             = Results_2ndCompound_others1_thin[22]
                        Tot_carbon_stems[t]         = Results_2ndCompound_others1_thin[23]
                        Tot_carbon_roots[t]         = Results_2ndCompound_others1_thin[24]
                        Tot_co2_stems[t]            = Results_2ndCompound_others1_thin[25]
                        Tot_co2_roots[t]            = Results_2ndCompound_others1_thin[26]

                for tree in trees:
                    t = tree
                    if (t in trees_pine)  and (len(spruce_toDelete) == 0): 
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        N_removed           = 0
                        R_vol_pine          = R_vol_pine
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        trees_dict[t]       = n_tree 
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]             
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
            
            #(mic_t == "High_pine") or (mic_t == "Medium_pine")                                            
            elif (Minor_species == "others_pine"): 
                for tree in trees:
                    t = tree                
                    if (t in trees_others) and (len(others_toDelete5) != 0): 
                        Results_1stCompound_others4_thin = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                     R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        N_removed                   = Results_1stCompound_others4_thin[0]
                        R_vol_birch                 = Results_1stCompound_others4_thin[1]
                        R_vol_others                = Results_1stCompound_others4_thin[2]
                        R_vol_ros                   = Results_1stCompound_others4_thin[3]
                        R_vol_warm                  = Results_1stCompound_others4_thin[4]
                        trees_dict[t]               = Results_1stCompound_others4_thin[5]
                        volsum[t]                   = Results_1stCompound_others4_thin[6]
                        vol_spruce[t]               = Results_1stCompound_others4_thin[7]
                        vol_pine[t]                 = Results_1stCompound_others4_thin[8]
                        vol_birch[t]                = Results_1stCompound_others4_thin[9]
                        vol_others[t]               = Results_1stCompound_others4_thin[10]
                        vol_ROS[t]                  = Results_1stCompound_others4_thin[11]
                        vol_warm[t]                 = Results_1stCompound_others4_thin[12]
                        R_SPulp[t]                  = Results_1stCompound_others4_thin[13]
                        R_SSaw[t]                   = Results_1stCompound_others4_thin[14]
                        R_HSaw[t]                   = Results_1stCompound_others4_thin[15]
                        R_HPulp[t]                  = Results_1stCompound_others4_thin[16]
                        R_PSaw[t]                   = Results_1stCompound_others4_thin[17]
                        R_PPulp[t]                  = Results_1stCompound_others4_thin[18]
                        G_before                    = Results_1stCompound_others4_thin[19]
                        R_BA                        = Results_1stCompound_others4_thin[20]
                        ba[t]                       = Results_1stCompound_others4_thin[21]
                        BGB[t]                      = Results_1stCompound_others4_thin[22]
                        Tot_co2[t]                  = Results_1stCompound_others4_thin[23]
                        Tot_biomass[t]              = Results_1stCompound_others4_thin[24]
                        Total_carbon[t]             = Results_1stCompound_others4_thin[25]
                        Tot_carbon_stems[t]         = Results_1stCompound_others4_thin[26]
                        Tot_carbon_roots[t]         = Results_1stCompound_others4_thin[27]
                        Tot_co2_stems[t]            = Results_1stCompound_others4_thin[28]
                        Tot_co2_roots[t]            = Results_1stCompound_others4_thin[29]
                        others_toDelete5.remove(str(t)) 
                            
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and len(others_toDelete5) == 0:                 
                        Results_2ndCompound_pine2_thin = self.Compound_pine_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                 Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                 N_removed, G_before)

                        N_removed                   = Results_2ndCompound_pine2_thin[0]
                        R_vol_spruce                = Results_2ndCompound_pine2_thin[1]
                        trees_dict[t]               = Results_2ndCompound_pine2_thin[2]
                        volsum[t]                   = Results_2ndCompound_pine2_thin[3]
                        vol_spruce[t]               = Results_2ndCompound_pine2_thin[4]
                        vol_pine[t]                 = Results_2ndCompound_pine2_thin[5]
                        vol_birch[t]                = Results_2ndCompound_pine2_thin[6]
                        vol_others[t]               = Results_2ndCompound_pine2_thin[7]
                        vol_ROS[t]                  = Results_2ndCompound_pine2_thin[8]
                        vol_warm[t]                 = Results_2ndCompound_pine2_thin[9]
                        R_SPulp[t]                  = Results_2ndCompound_pine2_thin[10]
                        R_SSaw[t]                   = Results_2ndCompound_pine2_thin[11]
                        R_HSaw[t]                   = Results_2ndCompound_pine2_thin[12]
                        R_HPulp[t]                  = Results_2ndCompound_pine2_thin[13]
                        R_PSaw[t]                   = Results_2ndCompound_pine2_thin[14]
                        R_PPulp[t]                  = Results_2ndCompound_pine2_thin[15]
                        G_before                    = Results_2ndCompound_pine2_thin[16]
                        R_BA                        = Results_2ndCompound_pine2_thin[17]
                        ba[t]                       = Results_2ndCompound_pine2_thin[18]
                        BGB[t]                      = Results_2ndCompound_pine2_thin[19]
                        Tot_co2[t]                  = Results_2ndCompound_pine2_thin[20]
                        Tot_biomass[t]              = Results_2ndCompound_pine2_thin[21]
                        Total_carbon[t]             = Results_2ndCompound_pine2_thin[22]
                        Tot_carbon_stems[t]         = Results_2ndCompound_pine2_thin[23]
                        Tot_carbon_roots[t]         = Results_2ndCompound_pine2_thin[24]
                        Tot_co2_stems[t]            = Results_2ndCompound_pine2_thin[25]
                        Tot_co2_roots[t]            = Results_2ndCompound_pine2_thin[26]
                        
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and len(others_toDelete5) == 0: 
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree 
                        N_removed           = 0
                        R_vol_spruce        = R_vol_spruce
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.  
                        
            #(mic_t == "High_pine") or (mic_t == "Medium_pine")           
            elif Minor_species ==  "others_some":
                for tree in trees:
                    t = tree
                    if t in trees_others:
                        Results_2ndCompound_others_some1_thin = self.SecondCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                           Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA,R_vol_birch,
                                                                                           R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        
                        N_removed                   = Results_2ndCompound_others_some1_thin[0]
                        R_vol_birch                 = Results_2ndCompound_others_some1_thin[1]
                        R_vol_others                = Results_2ndCompound_others_some1_thin[2]
                        R_vol_ros                   = Results_2ndCompound_others_some1_thin[3]
                        R_vol_warm                  = Results_2ndCompound_others_some1_thin[4]
                        trees_dict                  = Results_2ndCompound_others_some1_thin[5]
                        volsum[t]                   = Results_2ndCompound_others_some1_thin[6]
                        vol_spruce[t]               = Results_2ndCompound_others_some1_thin[7]
                        vol_pine[t]                 = Results_2ndCompound_others_some1_thin[8]
                        vol_birch[t]                = Results_2ndCompound_others_some1_thin[9]
                        vol_others[t]               = Results_2ndCompound_others_some1_thin[10]
                        vol_ROS[t]                  = Results_2ndCompound_others_some1_thin[11]
                        vol_warm[t]                 = Results_2ndCompound_others_some1_thin[12]
                        R_SPulp[t]                  = Results_2ndCompound_others_some1_thin[13]
                        R_SSaw[t]                   = Results_2ndCompound_others_some1_thin[14]
                        R_HSaw[t]                   = Results_2ndCompound_others_some1_thin[15]
                        R_HPulp[t]                  = Results_2ndCompound_others_some1_thin[16]
                        R_PSaw[t]                   = Results_2ndCompound_others_some1_thin[17]
                        R_PPulp[t]                  = Results_2ndCompound_others_some1_thin[18]
                        G_before                    = Results_2ndCompound_others_some1_thin[19]
                        R_BA                        = Results_2ndCompound_others_some1_thin[20]
                        ba[t]                       = Results_2ndCompound_others_some1_thin[21]                  
                        BGB[t]                      = Results_2ndCompound_others_some1_thin[22]
                        Tot_co2[t]                  = Results_2ndCompound_others_some1_thin[23]
                        Tot_biomass[t]              = Results_2ndCompound_others_some1_thin[24]
                        Total_carbon[t]             = Results_2ndCompound_others_some1_thin[25]
                        Tot_carbon_stems[t]         = Results_2ndCompound_others_some1_thin[26]
                        Tot_carbon_roots[t]         = Results_2ndCompound_others_some1_thin[27]
                        Tot_co2_stems[t]            = Results_2ndCompound_others_some1_thin[28]
                        Tot_co2_roots[t]            = Results_2ndCompound_others_some1_thin[29]
                    
                    else:
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        N_removed           = 0
                        R_vol_spruce        = R_vol_pine
                        R_vol_pine          = R_vol_pine
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]                       
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.
            
            #(mic_t == "High_pine") or (mic_t == "Medium_pine")
            elif (Minor_species ==  "spruce_only"):
                for tree in trees:
                    t = tree
                    if t in trees_spruce:
                        Results_1Compound_Spruce_only_thin = self.Compound_Spruce_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                       N_removed, G_before)
                        N_removed                   = Results_1Compound_Spruce_only_thin[0]
                        R_vol_spruce                = Results_1Compound_Spruce_only_thin[1]
                        trees_dict[t]               = Results_1Compound_Spruce_only_thin[2]
                        volsum[t]                   = Results_1Compound_Spruce_only_thin[3]
                        vol_spruce[t]               = Results_1Compound_Spruce_only_thin[4]
                        vol_pine[t]                 = Results_1Compound_Spruce_only_thin[5]
                        vol_birch[t]                = Results_1Compound_Spruce_only_thin[6]
                        vol_others[t]               = Results_1Compound_Spruce_only_thin[7]
                        vol_ROS[t]                  = Results_1Compound_Spruce_only_thin[8]
                        vol_warm[t]                 = Results_1Compound_Spruce_only_thin[9]
                        R_SPulp[t]                  = Results_1Compound_Spruce_only_thin[10]
                        R_SSaw[t]                   = Results_1Compound_Spruce_only_thin[11]
                        R_HSaw[t]                   = Results_1Compound_Spruce_only_thin[12]
                        R_HPulp[t]                  = Results_1Compound_Spruce_only_thin[13]
                        R_PSaw[t]                   = Results_1Compound_Spruce_only_thin[14]
                        R_PPulp[t]                  = Results_1Compound_Spruce_only_thin[15]
                        G_before                    = Results_1Compound_Spruce_only_thin[16]
                        R_BA                        = Results_1Compound_Spruce_only_thin[17]
                        ba[t]                       = Results_1Compound_Spruce_only_thin[18]
                        BGB[t]                      = Results_1Compound_Spruce_only_thin[19]
                        Tot_co2[t]                  = Results_1Compound_Spruce_only_thin[20]
                        Tot_biomass[t]              = Results_1Compound_Spruce_only_thin[21]
                        Total_carbon[t]             = Results_1Compound_Spruce_only_thin[22]
                        Tot_carbon_stems[t]         = Results_1Compound_Spruce_only_thin[23]
                        Tot_carbon_roots[t]         = Results_1Compound_Spruce_only_thin[24]
                        Tot_co2_stems[t]            = Results_1Compound_Spruce_only_thin[25]
                        Tot_co2_roots[t]            = Results_1Compound_Spruce_only_thin[26]
                        
                    else:
                        for t in trees: 
                            n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t]       = n_tree
                            N_removed           = 0
                            R_vol_pine          = R_vol_pine
                            G_before            = G_before
                            R_BA                = R_BA
                            ba[t]               = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                            volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_PSaw[t]           = 0.
                            R_PPulp[t]          = 0.
                            R_HSaw[t]           = 0.
                            R_HPulp[t]          = 0.
                            R_SSaw[t]           = 0.
                            R_SPulp[t]          = 0.  
            
            #(mic_t == "High_pine") or (mic_t == "Medium_pine")
            elif (Minor_species ==  "pine_only"):
                for tree in trees:
                    t = tree
                    if t in trees_pine:
                        Results_1Compound_pine1_only_thin = self.Compound_pine_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                   N_removed, G_before)
                        N_removed                   = Results_1Compound_pine1_only_thin[0]
                        R_vol_pine                  = Results_1Compound_pine1_only_thin[1]
                        trees_dict[t]               = Results_1Compound_pine1_only_thin[2]
                        volsum[t]                   = Results_1Compound_pine1_only_thin[3]
                        vol_spruce[t]               = Results_1Compound_pine1_only_thin[4]
                        vol_pine[t]                 = Results_1Compound_pine1_only_thin[5]
                        vol_birch[t]                = Results_1Compound_pine1_only_thin[6]
                        vol_others[t]               = Results_1Compound_pine1_only_thin[7]
                        vol_ROS[t]                  = Results_1Compound_pine1_only_thin[8]
                        vol_warm[t]                 = Results_1Compound_pine1_only_thin[9]
                        R_SPulp[t]                  = Results_1Compound_pine1_only_thin[10]
                        R_SSaw[t]                   = Results_1Compound_pine1_only_thin[11]
                        R_HSaw[t]                   = Results_1Compound_pine1_only_thin[12]
                        R_HPulp[t]                  = Results_1Compound_pine1_only_thin[13]
                        R_PSaw[t]                   = Results_1Compound_pine1_only_thin[14]
                        R_PPulp[t]                  = Results_1Compound_pine1_only_thin[15]
                        G_before                    = Results_1Compound_pine1_only_thin[16]
                        R_BA                        = Results_1Compound_pine1_only_thin[17]
                        ba[t]                       = Results_1Compound_pine1_only_thin[18]
                        BGB[t]                      = Results_1Compound_pine1_only_thin[19]
                        Tot_co2[t]                  = Results_1Compound_pine1_only_thin[20]
                        Tot_biomass[t]              = Results_1Compound_pine1_only_thin[21]
                        Total_carbon[t]             = Results_1Compound_pine1_only_thin[22]
                        Tot_carbon_stems[t]         = Results_1Compound_pine1_only_thin[23]
                        Tot_carbon_roots[t]         = Results_1Compound_pine1_only_thin[24]
                        Tot_co2_stems[t]            = Results_1Compound_pine1_only_thin[25]
                        Tot_co2_roots[t]            = Results_1Compound_pine1_only_thin[26]
                                
                    else:
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        N_removed           = 0
                        R_vol_spruce        = R_vol_spruce
                        R_vol_birch         = R_vol_birch
                        R_vol_others        = R_vol_others
                        R_vol_ros           = R_vol_ros
                        R_vol_warm          = R_vol_warm
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]                       
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                        
            #(mic_t == "High_pine") or (mic_t == "Medium_pine")                    
            elif (Minor_species == "others_spruce"): 
                for tree in trees:
                    t = tree                    
                    if (t in trees_others) and (len(others_toDelete) != 0): 
                        Results_1stCompound_others1_thin = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,  R_BA, R_vol_birch,
                                                                                     R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        N_removed                   = Results_1stCompound_others1_thin[0]
                        R_vol_birch                 = Results_1stCompound_others1_thin[1]
                        R_vol_others                = Results_1stCompound_others1_thin[2]
                        R_vol_ros                   = Results_1stCompound_others1_thin[3]
                        R_vol_warm                  = Results_1stCompound_others1_thin[4]
                        trees_dict[t]               = Results_1stCompound_others1_thin[5]
                        volsum[t]                   = Results_1stCompound_others1_thin[6]
                        vol_spruce[t]               = Results_1stCompound_others1_thin[7]
                        vol_pine[t]                 = Results_1stCompound_others1_thin[8]
                        vol_birch[t]                = Results_1stCompound_others1_thin[9]
                        vol_others[t]               = Results_1stCompound_others1_thin[10]
                        vol_ROS[t]                  = Results_1stCompound_others1_thin[11]
                        vol_warm[t]                 = Results_1stCompound_others1_thin[12]
                        R_SPulp[t]                  = Results_1stCompound_others1_thin[13]
                        R_SSaw[t]                   = Results_1stCompound_others1_thin[14]
                        R_HSaw[t]                   = Results_1stCompound_others1_thin[15]
                        R_HPulp[t]                  = Results_1stCompound_others1_thin[16]
                        R_PSaw[t]                   = Results_1stCompound_others1_thin[17]
                        R_PPulp[t]                  = Results_1stCompound_others1_thin[18]
                        G_before                    = Results_1stCompound_others1_thin[19]
                        R_BA                        = Results_1stCompound_others1_thin[20]
                        ba[t]                       = Results_1stCompound_others1_thin[21]
                        BGB[t]                      = Results_1stCompound_others1_thin[22]
                        Tot_co2[t]                  = Results_1stCompound_others1_thin[23]
                        Tot_biomass[t]              = Results_1stCompound_others1_thin[24]
                        Total_carbon[t]             = Results_1stCompound_others1_thin[25]
                        Tot_carbon_stems[t]         = Results_1stCompound_others1_thin[26]
                        Tot_carbon_roots[t]         = Results_1stCompound_others1_thin[27]
                        Tot_co2_stems[t]            = Results_1stCompound_others1_thin[28]
                        Tot_co2_roots[t]            = Results_1stCompound_others1_thin[29]
                        others_toDelete.remove(str(t))
                            
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and len(others_toDelete) == 0:                 
                        Results_2ndCompound_Spruce1_thin = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                     N_removed, G_before)
                        N_removed                   = Results_2ndCompound_Spruce1_thin[0]
                        R_vol_spruce                = Results_2ndCompound_Spruce1_thin[1]
                        trees_dict[t]               = Results_2ndCompound_Spruce1_thin[2]
                        volsum[t]                   = Results_2ndCompound_Spruce1_thin[3]
                        vol_spruce[t]               = Results_2ndCompound_Spruce1_thin[4]
                        vol_pine[t]                 = Results_2ndCompound_Spruce1_thin[5]
                        vol_birch[t]                = Results_2ndCompound_Spruce1_thin[6]
                        vol_others[t]               = Results_2ndCompound_Spruce1_thin[7]
                        vol_ROS[t]                  = Results_2ndCompound_Spruce1_thin[8]
                        vol_warm[t]                 = Results_2ndCompound_Spruce1_thin[9]
                        R_SPulp[t]                  = Results_2ndCompound_Spruce1_thin[10]
                        R_SSaw[t]                   = Results_2ndCompound_Spruce1_thin[11]
                        R_HSaw[t]                   = Results_2ndCompound_Spruce1_thin[12]
                        R_HPulp[t]                  = Results_2ndCompound_Spruce1_thin[13]
                        R_PSaw[t]                   = Results_2ndCompound_Spruce1_thin[14]
                        R_PPulp[t]                  = Results_2ndCompound_Spruce1_thin[15]
                        G_before                    = Results_2ndCompound_Spruce1_thin[16]
                        R_BA                        = Results_2ndCompound_Spruce1_thin[17]
                        ba[t]                       = Results_2ndCompound_Spruce1_thin[18]
                        BGB[t]                      = Results_2ndCompound_Spruce1_thin[19]
                        Tot_co2[t]                  = Results_2ndCompound_Spruce1_thin[20]
                        Tot_biomass[t]              = Results_2ndCompound_Spruce1_thin[21]
                        Total_carbon[t]             = Results_2ndCompound_Spruce1_thin[22]
                        Tot_carbon_stems[t]         = Results_2ndCompound_Spruce1_thin[23]
                        Tot_carbon_roots[t]         = Results_2ndCompound_Spruce1_thin[24]
                        Tot_co2_stems[t]            = Results_2ndCompound_Spruce1_thin[25]
                        Tot_co2_roots[t]            = Results_2ndCompound_Spruce1_thin[26]

                for tree in trees: 
                    t = tree
                    if (t in trees_pine) and len(others_toDelete) == 0: 
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        N_removed           = 0
                        R_vol_pine          = R_vol_pine
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.  
            
                        
            #(mic_t == "High_pine") or (mic_t == "Medium_pine")
            if (Minor_species ==  "spruce_pine"):
                for tree in trees:
                    t= tree
                    if (t in trees_spruce) and (len(spruce_toDelete8) != 0): 
                        Results_1stCompound_spruce3_thin = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                   N_removed, G_before)
                        N_removed                  = Results_1stCompound_spruce3_thin[0]
                        R_vol_spruce               = Results_1stCompound_spruce3_thin[1]
                        trees_dict[t]              = Results_1stCompound_spruce3_thin[2]
                        volsum[t]                  = Results_1stCompound_spruce3_thin[3]
                        vol_spruce[t]              = Results_1stCompound_spruce3_thin[4] 
                        vol_pine[t]                = Results_1stCompound_spruce3_thin[5]
                        vol_birch[t]               = Results_1stCompound_spruce3_thin[6]
                        vol_others[t]              = Results_1stCompound_spruce3_thin[7]
                        vol_ROS[t]                 = Results_1stCompound_spruce3_thin[8]
                        vol_warm[t]                = Results_1stCompound_spruce3_thin[9]
                        R_SPulp[t]                 = Results_1stCompound_spruce3_thin[10]
                        R_SSaw[t]                  = Results_1stCompound_spruce3_thin[11]
                        R_HSaw[t]                  = Results_1stCompound_spruce3_thin[12]
                        R_HPulp[t]                 = Results_1stCompound_spruce3_thin[13]
                        R_PSaw[t]                  = Results_1stCompound_spruce3_thin[14]
                        R_PPulp[t]                 = Results_1stCompound_spruce3_thin[15]
                        G_before                   = Results_1stCompound_spruce3_thin[16]
                        R_BA                       = Results_1stCompound_spruce3_thin[17]
                        ba[t]                      = Results_1stCompound_spruce3_thin[18]
                        BGB[t]                     = Results_1stCompound_spruce3_thin[19]
                        Tot_co2[t]                 = Results_1stCompound_spruce3_thin[20]
                        Tot_biomass[t]             = Results_1stCompound_spruce3_thin[21]
                        Total_carbon[t]            = Results_1stCompound_spruce3_thin[22]
                        Tot_carbon_stems[t]        = Results_1stCompound_spruce3_thin[23]
                        Tot_carbon_roots[t]        = Results_1stCompound_spruce3_thin[24]
                        Tot_co2_stems[t]           = Results_1stCompound_spruce3_thin[25]
                        Tot_co2_roots[t]           = Results_1stCompound_spruce3_thin[26]
                        spruce_toDelete8.remove(str(t))
                            
                for tree in trees:
                    t = tree
                    if (t in trees_pine)  and len(spruce_toDelete8) == 0: 
                        Results_2ndCompound_pine4_thin = self.LastCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                              Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine, 
                                                                              N_removed, G_before)
                        N_removed               = Results_2ndCompound_pine4_thin[0]
                        R_vol_pine              = Results_2ndCompound_pine4_thin[1]
                        trees_dict[t]           = Results_2ndCompound_pine4_thin[2]
                        volsum[t]               = Results_2ndCompound_pine4_thin[3]
                        vol_spruce[t]           = Results_2ndCompound_pine4_thin[4]
                        vol_pine[t]             = Results_2ndCompound_pine4_thin[5]
                        vol_birch[t]            = Results_2ndCompound_pine4_thin[6]
                        vol_others[t]           = Results_2ndCompound_pine4_thin[7]
                        vol_ROS[t]              = Results_2ndCompound_pine4_thin[8]
                        vol_warm[t]             = Results_2ndCompound_pine4_thin[9]
                        R_SPulp[t]              = Results_2ndCompound_pine4_thin[10]
                        R_SSaw[t]               = Results_2ndCompound_pine4_thin[11]
                        R_HSaw[t]               = Results_2ndCompound_pine4_thin[12]
                        R_HPulp[t]              = Results_2ndCompound_pine4_thin[13]
                        R_PSaw[t]               = Results_2ndCompound_pine4_thin[14]
                        R_PPulp[t]              = Results_2ndCompound_pine4_thin[15]
                        G_before                = Results_2ndCompound_pine4_thin[16]
                        R_BA                    = Results_2ndCompound_pine4_thin[17]
                        ba[t]                   = Results_2ndCompound_pine4_thin[18]
                        BGB[t]                  = Results_2ndCompound_pine4_thin[19]
                        Tot_co2[t]              = Results_2ndCompound_pine4_thin[20]
                        Tot_biomass[t]          = Results_2ndCompound_pine4_thin[21]
                        Total_carbon[t]         = Results_2ndCompound_pine4_thin[22]
                        Tot_carbon_stems[t]     = Results_2ndCompound_pine4_thin[23]
                        Tot_carbon_roots[t]     = Results_2ndCompound_pine4_thin[24]
                        Tot_co2_stems[t]        = Results_2ndCompound_pine4_thin[25]
                        Tot_co2_roots[t]        = Results_2ndCompound_pine4_thin[26]

                                
                for t in trees:
                    if (t in trees_others)  and (len(spruce_toDelete8) == 0): 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 
                        
                        
            #(mic_t == "High_pine") or (mic_t == "Medium_pine")
            elif (Minor_species == "spruce_others_pine"):
                for tree in trees:
                    t= tree                    
                    if (t in trees_spruce) and (len(spruce_toDelete2) != 0):                   
                        Results_1stCompound_spruce2_thin = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                     N_removed, G_before)
                        N_removed                  = Results_1stCompound_spruce2_thin[0]
                        R_vol_spruce               = Results_1stCompound_spruce2_thin[1]
                        trees_dict[t]              = Results_1stCompound_spruce2_thin[2]
                        volsum[t]                  = Results_1stCompound_spruce2_thin[3]
                        vol_spruce[t]              = Results_1stCompound_spruce2_thin[4]
                        vol_pine[t]                = Results_1stCompound_spruce2_thin[5]
                        vol_birch[t]               = Results_1stCompound_spruce2_thin[6]
                        vol_others[t]              = Results_1stCompound_spruce2_thin[7]
                        vol_ROS[t]                 = Results_1stCompound_spruce2_thin[8]
                        vol_warm[t]                = Results_1stCompound_spruce2_thin[9]
                        R_SPulp[t]                 = Results_1stCompound_spruce2_thin[10]
                        R_SSaw[t]                  = Results_1stCompound_spruce2_thin[11]
                        R_HSaw[t]                  = Results_1stCompound_spruce2_thin[12]
                        R_HPulp[t]                 = Results_1stCompound_spruce2_thin[13]
                        R_PSaw[t]                  = Results_1stCompound_spruce2_thin[14]
                        R_PPulp[t]                 = Results_1stCompound_spruce2_thin[15]
                        G_before                   = Results_1stCompound_spruce2_thin[16]
                        R_BA                       = Results_1stCompound_spruce2_thin[17]
                        ba[t]                      = Results_1stCompound_spruce2_thin[18]
                        BGB[t]                     = Results_1stCompound_spruce2_thin[19]
                        Tot_co2[t]                 = Results_1stCompound_spruce2_thin[20]
                        Tot_biomass[t]             = Results_1stCompound_spruce2_thin[21]
                        Total_carbon[t]            = Results_1stCompound_spruce2_thin[22]
                        Tot_carbon_stems[t]        = Results_1stCompound_spruce2_thin[23]
                        Tot_carbon_roots[t]        = Results_1stCompound_spruce2_thin[24]
                        Tot_co2_stems[t]           = Results_1stCompound_spruce2_thin[25]
                        Tot_co2_roots[t]           = Results_1stCompound_spruce2_thin[26]
                        spruce_toDelete2.remove(str(t))
                                                                                  
                for tree in trees:
                    t = tree                   
                    if (t in trees_others) and (len(spruce_toDelete2) == 0) and (len(others_toDelete2) != 0):                                            
                        Results_MCompound_others1_thin = self.MiddleCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                    Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                    R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        N_removed                   = Results_MCompound_others1_thin[0]
                        R_vol_birch                 = Results_MCompound_others1_thin[1]  
                        R_vol_others                = Results_MCompound_others1_thin[2]
                        R_vol_ros                   = Results_MCompound_others1_thin[3]
                        R_vol_warm                  = Results_MCompound_others1_thin[4]
                        trees_dict[t]               = Results_MCompound_others1_thin[5]
                        volsum[t]                   = Results_MCompound_others1_thin[6]
                        vol_spruce[t]               = Results_MCompound_others1_thin[7]
                        vol_pine[t]                 = Results_MCompound_others1_thin[8]
                        vol_birch[t]                = Results_MCompound_others1_thin[9]
                        vol_others[t]               = Results_MCompound_others1_thin[10]
                        vol_ROS[t]                  = Results_MCompound_others1_thin[11]
                        vol_warm[t]                 = Results_MCompound_others1_thin[12]
                        R_SPulp[t]                  = Results_MCompound_others1_thin[13]
                        R_SSaw[t]                   = Results_MCompound_others1_thin[14]
                        R_HSaw[t]                   = Results_MCompound_others1_thin[15]
                        R_HPulp[t]                  = Results_MCompound_others1_thin[16]
                        R_PSaw[t]                   = Results_MCompound_others1_thin[17]
                        R_PPulp[t]                  = Results_MCompound_others1_thin[18]
                        G_before                    = Results_MCompound_others1_thin[19]
                        R_BA                        = Results_MCompound_others1_thin[20]
                        ba[t]                       = Results_MCompound_others1_thin[21]
                        BGB[t]                      = Results_MCompound_others1_thin[22]
                        Tot_co2[t]                  = Results_MCompound_others1_thin[23]
                        Tot_biomass[t]              = Results_MCompound_others1_thin[24]
                        Total_carbon[t]             = Results_MCompound_others1_thin[25]
                        Tot_carbon_stems[t]         = Results_MCompound_others1_thin[26]
                        Tot_carbon_roots[t]         = Results_MCompound_others1_thin[27]
                        Tot_co2_stems[t]            = Results_MCompound_others1_thin[28]
                        Tot_co2_roots[t]            = Results_MCompound_others1_thin[29]
                        others_toDelete2.remove(str(t))
                        
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and (len(others_toDelete2) == 0) and (len(spruce_toDelete2) == 0): 
                        Results_LastCompound_pine1_thin = self.LastCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                 Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine, 
                                                                                 N_removed, G_before)
                        N_removed                   = Results_LastCompound_pine1_thin[0]
                        R_vol_pine                  = Results_LastCompound_pine1_thin[1]
                        trees_dict[t]               = Results_LastCompound_pine1_thin[2]
                        volsum[t]                   = Results_LastCompound_pine1_thin[3]
                        vol_spruce[t]               = Results_LastCompound_pine1_thin[4]
                        vol_pine[t]                 = Results_LastCompound_pine1_thin[5]
                        vol_birch[t]                = Results_LastCompound_pine1_thin[6]
                        vol_others[t]               = Results_LastCompound_pine1_thin[7]
                        vol_ROS[t]                  = Results_LastCompound_pine1_thin[8]
                        vol_warm[t]                 = Results_LastCompound_pine1_thin[9]
                        R_SPulp[t]                  = Results_LastCompound_pine1_thin[10]
                        R_SSaw[t]                   = Results_LastCompound_pine1_thin[11]
                        R_HSaw[t]                   = Results_LastCompound_pine1_thin[12]
                        R_HPulp[t]                  = Results_LastCompound_pine1_thin[13]
                        R_PSaw[t]                   = Results_LastCompound_pine1_thin[14]
                        R_PPulp[t]                  = Results_LastCompound_pine1_thin[15]
                        G_before                    = Results_LastCompound_pine1_thin[16]
                        R_BA                        = Results_LastCompound_pine1_thin[17]
                        ba[t]                       = Results_LastCompound_pine1_thin[18]
                        BGB[t]                      = Results_LastCompound_pine1_thin[19]
                        Tot_co2[t]                  = Results_LastCompound_pine1_thin[20]
                        Tot_biomass[t]              = Results_LastCompound_pine1_thin[21]
                        Total_carbon[t]             = Results_LastCompound_pine1_thin[22]
                        Tot_carbon_stems[t]         = Results_LastCompound_pine1_thin[23]
                        Tot_carbon_roots[t]         = Results_LastCompound_pine1_thin[24]
                        Tot_co2_stems[t]            = Results_LastCompound_pine1_thin[25]
                        Tot_co2_roots[t]            = Results_LastCompound_pine1_thin[26]
                                                

                
        elif (mic_t == "High_spruce") or (mic_t == "Medium_spruce"):
            #(mic_t == "High_spruce") or (mic_t == "Medium_spruce")
            if (Minor_species ==  "pine_others"):
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and (len(pine_toDelete2) != 0):
                        Results_1stCompound_pine1_thin = self.firstCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                 Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine,
                                                                                 N_removed, G_before)
                        N_removed                  = Results_1stCompound_pine1_thin[0]
                        R_vol_pine                 = Results_1stCompound_pine1_thin[1]
                        trees_dict[t]              = Results_1stCompound_pine1_thin[2]
                        volsum[t]                  = Results_1stCompound_pine1_thin[3]
                        vol_spruce[t]              = Results_1stCompound_pine1_thin[4]
                        vol_pine[t]                = Results_1stCompound_pine1_thin[5]
                        vol_birch[t]               = Results_1stCompound_pine1_thin[6]
                        vol_others[t]              = Results_1stCompound_pine1_thin[7]
                        vol_ROS[t]                 = Results_1stCompound_pine1_thin[8]
                        vol_warm[t]                = Results_1stCompound_pine1_thin[9]
                        R_SPulp[t]                 = Results_1stCompound_pine1_thin[10]
                        R_SSaw[t]                  = Results_1stCompound_pine1_thin[11]
                        R_HSaw[t]                  = Results_1stCompound_pine1_thin[12]
                        R_HPulp[t]                 = Results_1stCompound_pine1_thin[13]
                        R_PSaw[t]                  = Results_1stCompound_pine1_thin[14]
                        R_PPulp[t]                 = Results_1stCompound_pine1_thin[15]
                        G_before                   = Results_1stCompound_pine1_thin[16]
                        R_BA                       = Results_1stCompound_pine1_thin[17]
                        ba[t]                      = Results_1stCompound_pine1_thin[18]
                        BGB[t]                     = Results_1stCompound_pine1_thin[19]
                        Tot_co2[t]                 = Results_1stCompound_pine1_thin[20]
                        Tot_biomass[t]             = Results_1stCompound_pine1_thin[21]
                        Total_carbon[t]            = Results_1stCompound_pine1_thin[22]
                        Tot_carbon_stems[t]        = Results_1stCompound_pine1_thin[23]
                        Tot_carbon_roots[t]        = Results_1stCompound_pine1_thin[24]
                        Tot_co2_stems[t]           = Results_1stCompound_pine1_thin[25]
                        Tot_co2_roots[t]           = Results_1stCompound_pine1_thin[26]
                        pine_toDelete2.remove(str(t))
                        
                            
                for tree in trees:
                    t = tree
                    if (t in trees_others)  and len(pine_toDelete2) == 0:               
                        Results_2ndCompound_others1_thin = self.SecondCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                      Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                      R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        
                        N_removed                   = Results_2ndCompound_others1_thin[0]
                        R_vol_birch                 = Results_2ndCompound_others1_thin[1]
                        R_vol_others                = Results_2ndCompound_others1_thin[2]
                        R_vol_ros                   = Results_2ndCompound_others1_thin[3]
                        R_vol_warm                  = Results_2ndCompound_others1_thin[4]
                        trees_dict[t]               = Results_2ndCompound_others1_thin[5]
                        volsum[t]                   = Results_2ndCompound_others1_thin[6]
                        vol_spruce[t]               = Results_2ndCompound_others1_thin[7]
                        vol_pine[t]                 = Results_2ndCompound_others1_thin[8]
                        vol_birch[t]                = Results_2ndCompound_others1_thin[9]
                        vol_others[t]               = Results_2ndCompound_others1_thin[10]
                        vol_ROS[t]                  = Results_2ndCompound_others1_thin[11]
                        vol_warm[t]                 = Results_2ndCompound_others1_thin[12]
                        R_SPulp[t]                  = Results_2ndCompound_others1_thin[13]
                        R_SSaw[t]                   = Results_2ndCompound_others1_thin[14]
                        R_HSaw[t]                   = Results_2ndCompound_others1_thin[15]
                        R_HPulp[t]                  = Results_2ndCompound_others1_thin[16]
                        R_PSaw[t]                   = Results_2ndCompound_others1_thin[17]
                        R_PPulp[t]                  = Results_2ndCompound_others1_thin[18]
                        G_before                    = Results_2ndCompound_others1_thin[19]
                        R_BA                        = Results_2ndCompound_others1_thin[20]
                        ba[t]                       = Results_2ndCompound_others1_thin[21]
                        BGB[t]                      = Results_2ndCompound_others1_thin[22]
                        Tot_co2[t]                  = Results_2ndCompound_others1_thin[23]
                        Tot_biomass[t]              = Results_2ndCompound_others1_thin[24]
                        Total_carbon[t]             = Results_2ndCompound_others1_thin[25]
                        Tot_carbon_stems[t]         = Results_2ndCompound_others1_thin[26]
                        Tot_carbon_roots[t]         = Results_2ndCompound_others1_thin[27]
                        Tot_co2_stems[t]            = Results_2ndCompound_others1_thin[28]
                        Tot_co2_roots[t]            = Results_2ndCompound_others1_thin[29]
                        
                                
                for tree in trees:
                    t = tree
                    if (t in trees_spruce)  and (len(pine_toDelete2) == 0): 
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        N_removed           = 0
                        R_vol_spruce        = R_vol_spruce
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]                        
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.                                                       
            
            #(mic_t == "High_spruce") or (mic_t == "Medium_spruce")
            elif Minor_species ==  "others_some":
                for tree in trees:
                    t = tree
                    if t in trees_others:
                        Results_2ndCompound_others_some2_thin = self.SecondCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                           Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA,R_vol_birch,
                                                                                           R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        
                        N_removed                   = Results_2ndCompound_others_some2_thin[0]
                        R_vol_birch                 = Results_2ndCompound_others_some2_thin[1]
                        R_vol_others                = Results_2ndCompound_others_some2_thin[2]
                        R_vol_ros                   = Results_2ndCompound_others_some2_thin[3]
                        R_vol_warm                  = Results_2ndCompound_others_some2_thin[4]
                        trees_dict                  = Results_2ndCompound_others_some2_thin[5]
                        volsum[t]                   = Results_2ndCompound_others_some2_thin[6]
                        vol_spruce[t]               = Results_2ndCompound_others_some2_thin[7]
                        vol_pine[t]                 = Results_2ndCompound_others_some2_thin[8]
                        vol_birch[t]                = Results_2ndCompound_others_some2_thin[9]
                        vol_others[t]               = Results_2ndCompound_others_some2_thin[10]
                        vol_ROS[t]                  = Results_2ndCompound_others_some2_thin[11]
                        vol_warm[t]                 = Results_2ndCompound_others_some2_thin[12]
                        R_SPulp[t]                  = Results_2ndCompound_others_some2_thin[13]
                        R_SSaw[t]                   = Results_2ndCompound_others_some2_thin[14]
                        R_HSaw[t]                   = Results_2ndCompound_others_some2_thin[15]
                        R_HPulp[t]                  = Results_2ndCompound_others_some2_thin[16]
                        R_PSaw[t]                   = Results_2ndCompound_others_some2_thin[17]
                        R_PPulp[t]                  = Results_2ndCompound_others_some2_thin[18]
                        G_before                    = Results_2ndCompound_others_some2_thin[19]
                        R_BA                        = Results_2ndCompound_others_some2_thin[20]
                        ba[t]                       = Results_2ndCompound_others_some2_thin[21]                  
                        BGB[t]                      = Results_2ndCompound_others_some2_thin[22]
                        Tot_co2[t]                  = Results_2ndCompound_others_some2_thin[23]
                        Tot_biomass[t]              = Results_2ndCompound_others_some2_thin[24]
                        Total_carbon[t]             = Results_2ndCompound_others_some2_thin[25]
                        Tot_carbon_stems[t]         = Results_2ndCompound_others_some2_thin[26]
                        Tot_carbon_roots[t]         = Results_2ndCompound_others_some2_thin[27]
                        Tot_co2_stems[t]            = Results_2ndCompound_others_some2_thin[28]
                        Tot_co2_roots[t]            = Results_2ndCompound_others_some2_thin[29]
                    
                    else:
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        N_removed           = 0
                        R_vol_spruce        = R_vol_pine
                        R_vol_pine          = R_vol_pine
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]                       
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.
                        
            # (mic_t == "High_spruce") or (mic_t == "Medium_spruce")                                   
            elif (Minor_species ==  "pine_spruce"):
                for tree in trees:
                    t = tree                                          
                    if (t in trees_pine) and (len(pine_toDelete4) != 0):                                                      
                        Results_1stCompound_pine3_thin = self.firstCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                               Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine,
                                                                               N_removed, G_before)
                        N_removed                  = Results_1stCompound_pine3_thin[0]
                        R_vol_pine                 = Results_1stCompound_pine3_thin[1]
                        trees_dict[t]              = Results_1stCompound_pine3_thin[2]
                        volsum[t]                  = Results_1stCompound_pine3_thin[3]
                        vol_spruce[t]              = Results_1stCompound_pine3_thin[4]
                        vol_pine[t]                = Results_1stCompound_pine3_thin[5]
                        vol_birch[t]               = Results_1stCompound_pine3_thin[6]
                        vol_others[t]              = Results_1stCompound_pine3_thin[7]
                        vol_ROS[t]                 = Results_1stCompound_pine3_thin[8]
                        vol_warm[t]                = Results_1stCompound_pine3_thin[9]
                        R_SPulp[t]                 = Results_1stCompound_pine3_thin[10]
                        R_SSaw[t]                  = Results_1stCompound_pine3_thin[11]
                        R_HSaw[t]                  = Results_1stCompound_pine3_thin[12]
                        R_HPulp[t]                 = Results_1stCompound_pine3_thin[13]
                        R_PSaw[t]                  = Results_1stCompound_pine3_thin[14]
                        R_PPulp[t]                 = Results_1stCompound_pine3_thin[15]
                        G_before                   = Results_1stCompound_pine3_thin[16]
                        R_BA                       = Results_1stCompound_pine3_thin[17]
                        ba[t]                      = Results_1stCompound_pine3_thin[18]
                        BGB[t]                     = Results_1stCompound_pine3_thin[19]
                        Tot_co2[t]                 = Results_1stCompound_pine3_thin[20]
                        Tot_biomass[t]             = Results_1stCompound_pine3_thin[21]
                        Total_carbon[t]            = Results_1stCompound_pine3_thin[22]
                        Tot_carbon_stems[t]        = Results_1stCompound_pine3_thin[23]
                        Tot_carbon_roots[t]        = Results_1stCompound_pine3_thin[24]
                        Tot_co2_stems[t]           = Results_1stCompound_pine3_thin[25]
                        Tot_co2_roots[t]           = Results_1stCompound_pine3_thin[26]
                        pine_toDelete4.remove(str(t))
                                                  
                            
                for tree in trees:
                    t = tree
                    if (t in trees_spruce)  and len(pine_toDelete4) == 0: 
                        Results_2ndCompound_Spruce3_thin = self.Compound_Spruce_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                   N_removed, G_before)
                        N_removed               = Results_2ndCompound_Spruce3_thin[0]
                        R_vol_spruce            = Results_2ndCompound_Spruce3_thin[1]
                        trees_dict[t]           = Results_2ndCompound_Spruce3_thin[2]
                        volsum[t]               = Results_2ndCompound_Spruce3_thin[3]
                        vol_spruce[t]           = Results_2ndCompound_Spruce3_thin[4]
                        vol_pine[t]             = Results_2ndCompound_Spruce3_thin[5]
                        vol_birch[t]            = Results_2ndCompound_Spruce3_thin[6]
                        vol_others[t]           = Results_2ndCompound_Spruce3_thin[7]
                        vol_ROS[t]              = Results_2ndCompound_Spruce3_thin[8]
                        vol_warm[t]             = Results_2ndCompound_Spruce3_thin[9]
                        R_SPulp[t]              = Results_2ndCompound_Spruce3_thin[10]
                        R_SSaw[t]               = Results_2ndCompound_Spruce3_thin[11]
                        R_HSaw[t]               = Results_2ndCompound_Spruce3_thin[12]
                        R_HPulp[t]              = Results_2ndCompound_Spruce3_thin[13]
                        R_PSaw[t]               = Results_2ndCompound_Spruce3_thin[14]
                        R_PPulp[t]              = Results_2ndCompound_Spruce3_thin[15]
                        G_before                = Results_2ndCompound_Spruce3_thin[16]
                        R_BA                    = Results_2ndCompound_Spruce3_thin[17]
                        ba[t]                   = Results_2ndCompound_Spruce3_thin[18]
                        BGB[t]                  = Results_2ndCompound_Spruce3_thin[19]
                        Tot_co2[t]              = Results_2ndCompound_Spruce3_thin[20]
                        Tot_biomass[t]          = Results_2ndCompound_Spruce3_thin[21]
                        Total_carbon[t]         = Results_2ndCompound_Spruce3_thin[22]
                        Tot_carbon_stems[t]     = Results_2ndCompound_Spruce3_thin[23]
                        Tot_carbon_roots[t]     = Results_2ndCompound_Spruce3_thin[24]
                        Tot_co2_stems[t]        = Results_2ndCompound_Spruce3_thin[25]
                        Tot_co2_roots[t]        = Results_2ndCompound_Spruce3_thin[26]
                        
                                
                for tree in trees:
                    t = tree
                    if (t in trees_others)  and (len(pine_toDelete4) == 0): 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree 
                        N_removed     = 0
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 
            
            # (mic_t == "High_spruce") or (mic_t == "Medium_spruce")  
            elif (Minor_species == "others_spruce"): 
                for tree in trees:
                    t = tree                    
                    if (t in trees_others) and (len(others1_toDelete) != 0): 
                        Results_1stCompound_others3_thin = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,  R_BA, R_vol_birch,
                                                                                     R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        N_removed                   = Results_1stCompound_others3_thin[0]
                        R_vol_birch                 = Results_1stCompound_others3_thin[1]
                        R_vol_others                = Results_1stCompound_others3_thin[2]
                        R_vol_ros                   = Results_1stCompound_others3_thin[3]
                        R_vol_warm                  = Results_1stCompound_others3_thin[4]
                        trees_dict[t]               = Results_1stCompound_others3_thin[5]
                        volsum[t]                   = Results_1stCompound_others3_thin[6]
                        vol_spruce[t]               = Results_1stCompound_others3_thin[7]
                        vol_pine[t]                 = Results_1stCompound_others3_thin[8]
                        vol_birch[t]                = Results_1stCompound_others3_thin[9]
                        vol_others[t]               = Results_1stCompound_others3_thin[10]
                        vol_ROS[t]                  = Results_1stCompound_others3_thin[11]
                        vol_warm[t]                 = Results_1stCompound_others3_thin[12]
                        R_SPulp[t]                  = Results_1stCompound_others3_thin[13]
                        R_SSaw[t]                   = Results_1stCompound_others3_thin[14]
                        R_HSaw[t]                   = Results_1stCompound_others3_thin[15]
                        R_HPulp[t]                  = Results_1stCompound_others3_thin[16]
                        R_PSaw[t]                   = Results_1stCompound_others3_thin[17]
                        R_PPulp[t]                  = Results_1stCompound_others3_thin[18]
                        G_before                    = Results_1stCompound_others3_thin[19]
                        R_BA                        = Results_1stCompound_others3_thin[20]
                        ba[t]                       = Results_1stCompound_others3_thin[21]
                        BGB[t]                      = Results_1stCompound_others3_thin[22]
                        Tot_co2[t]                  = Results_1stCompound_others3_thin[23]
                        Tot_biomass[t]              = Results_1stCompound_others3_thin[24]
                        Total_carbon[t]             = Results_1stCompound_others3_thin[25]
                        Tot_carbon_stems[t]         = Results_1stCompound_others3_thin[26]
                        Tot_carbon_roots[t]         = Results_1stCompound_others3_thin[27]
                        Tot_co2_stems[t]            = Results_1stCompound_others3_thin[28]
                        Tot_co2_roots[t]            = Results_1stCompound_others3_thin[29]
                        others1_toDelete.remove(str(t))
                            
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and len(others1_toDelete) == 0:                 
                        Results_2ndCompound_Spruce2_thin = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                     N_removed, G_before)
                        N_removed                   = Results_2ndCompound_Spruce2_thin[0]
                        R_vol_spruce                = Results_2ndCompound_Spruce2_thin[1]
                        trees_dict[t]               = Results_2ndCompound_Spruce2_thin[2]
                        volsum[t]                   = Results_2ndCompound_Spruce2_thin[3]
                        vol_spruce[t]               = Results_2ndCompound_Spruce2_thin[4]
                        vol_pine[t]                 = Results_2ndCompound_Spruce2_thin[5]
                        vol_birch[t]                = Results_2ndCompound_Spruce2_thin[6]
                        vol_others[t]               = Results_2ndCompound_Spruce2_thin[7]
                        vol_ROS[t]                  = Results_2ndCompound_Spruce2_thin[8]
                        vol_warm[t]                 = Results_2ndCompound_Spruce2_thin[9]
                        R_SPulp[t]                  = Results_2ndCompound_Spruce2_thin[10]
                        R_SSaw[t]                   = Results_2ndCompound_Spruce2_thin[11]
                        R_HSaw[t]                   = Results_2ndCompound_Spruce2_thin[12]
                        R_HPulp[t]                  = Results_2ndCompound_Spruce2_thin[13]
                        R_PSaw[t]                   = Results_2ndCompound_Spruce2_thin[14]
                        R_PPulp[t]                  = Results_2ndCompound_Spruce2_thin[15]
                        G_before                    = Results_2ndCompound_Spruce2_thin[16]
                        R_BA                        = Results_2ndCompound_Spruce2_thin[17]
                        ba[t]                       = Results_2ndCompound_Spruce2_thin[18]
                        BGB[t]                      = Results_2ndCompound_Spruce2_thin[19]
                        Tot_co2[t]                  = Results_2ndCompound_Spruce2_thin[20]
                        Tot_biomass[t]              = Results_2ndCompound_Spruce2_thin[21]
                        Total_carbon[t]             = Results_2ndCompound_Spruce2_thin[22]
                        Tot_carbon_stems[t]         = Results_2ndCompound_Spruce2_thin[23]
                        Tot_carbon_roots[t]         = Results_2ndCompound_Spruce2_thin[24]
                        Tot_co2_stems[t]            = Results_2ndCompound_Spruce2_thin[25]
                        Tot_co2_roots[t]            = Results_2ndCompound_Spruce2_thin[26]

                for tree in trees: 
                    t = tree
                    if (t in trees_pine) and len(others1_toDelete) == 0: 
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        N_removed           = 0
                        R_vol_pine          = R_vol_pine
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.  
                        
            # (mic_t == "High_spruce") or (mic_t == "Medium_spruce") 
            elif (Minor_species ==  "spruce_only"):
                for tree in trees:
                    t = tree
                    if t in trees_spruce:
                        Results_1Compound_Spruce1_only_thin = self.Compound_Spruce_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                       N_removed, G_before)
                        N_removed                   = Results_1Compound_Spruce1_only_thin[0]
                        R_vol_spruce                = Results_1Compound_Spruce1_only_thin[1]
                        trees_dict[t]               = Results_1Compound_Spruce1_only_thin[2]
                        volsum[t]                   = Results_1Compound_Spruce1_only_thin[3]
                        vol_spruce[t]               = Results_1Compound_Spruce1_only_thin[4]
                        vol_pine[t]                 = Results_1Compound_Spruce1_only_thin[5]
                        vol_birch[t]                = Results_1Compound_Spruce1_only_thin[6]
                        vol_others[t]               = Results_1Compound_Spruce1_only_thin[7]
                        vol_ROS[t]                  = Results_1Compound_Spruce1_only_thin[8]
                        vol_warm[t]                 = Results_1Compound_Spruce1_only_thin[9]
                        R_SPulp[t]                  = Results_1Compound_Spruce1_only_thin[10]
                        R_SSaw[t]                   = Results_1Compound_Spruce1_only_thin[11]
                        R_HSaw[t]                   = Results_1Compound_Spruce1_only_thin[12]
                        R_HPulp[t]                  = Results_1Compound_Spruce1_only_thin[13]
                        R_PSaw[t]                   = Results_1Compound_Spruce1_only_thin[14]
                        R_PPulp[t]                  = Results_1Compound_Spruce1_only_thin[15]
                        G_before                    = Results_1Compound_Spruce1_only_thin[16]
                        R_BA                        = Results_1Compound_Spruce1_only_thin[17]
                        ba[t]                       = Results_1Compound_Spruce1_only_thin[18]
                        BGB[t]                      = Results_1Compound_Spruce1_only_thin[19]
                        Tot_co2[t]                  = Results_1Compound_Spruce1_only_thin[20]
                        Tot_biomass[t]              = Results_1Compound_Spruce1_only_thin[21]
                        Total_carbon[t]             = Results_1Compound_Spruce1_only_thin[22]
                        Tot_carbon_stems[t]         = Results_1Compound_Spruce1_only_thin[23]
                        Tot_carbon_roots[t]         = Results_1Compound_Spruce1_only_thin[24]
                        Tot_co2_stems[t]            = Results_1Compound_Spruce1_only_thin[25]
                        Tot_co2_roots[t]            = Results_1Compound_Spruce1_only_thin[26]
                        
                    else:
                        for t in trees: 
                            n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t]       = n_tree
                            N_removed           = 0
                            R_vol_pine          = R_vol_pine
                            G_before            = G_before
                            R_BA                = R_BA
                            ba[t]               = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                            volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_PSaw[t]           = 0.
                            R_PPulp[t]          = 0.
                            R_HSaw[t]           = 0.
                            R_HPulp[t]          = 0.
                            R_SSaw[t]           = 0.
                            R_SPulp[t]          = 0.             
            
            # (mic_t == "High_spruce") or (mic_t == "Medium_spruce") 
            elif (Minor_species ==  "pine_only"):
                for tree in trees:
                    t = tree
                    if t in trees_pine:
                        Results_1Compound_pine_only_thin = self.Compound_pine_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                   N_removed, G_before)
                        N_removed                   = Results_1Compound_pine_only_thin[0]
                        R_vol_pine                  = Results_1Compound_pine_only_thin[1]
                        trees_dict[t]               = Results_1Compound_pine_only_thin[2]
                        volsum[t]                   = Results_1Compound_pine_only_thin[3]
                        vol_spruce[t]               = Results_1Compound_pine_only_thin[4]
                        vol_pine[t]                 = Results_1Compound_pine_only_thin[5]
                        vol_birch[t]                = Results_1Compound_pine_only_thin[6]
                        vol_others[t]               = Results_1Compound_pine_only_thin[7]
                        vol_ROS[t]                  = Results_1Compound_pine_only_thin[8]
                        vol_warm[t]                 = Results_1Compound_pine_only_thin[9]
                        R_SPulp[t]                  = Results_1Compound_pine_only_thin[10]
                        R_SSaw[t]                   = Results_1Compound_pine_only_thin[11]
                        R_HSaw[t]                   = Results_1Compound_pine_only_thin[12]
                        R_HPulp[t]                  = Results_1Compound_pine_only_thin[13]
                        R_PSaw[t]                   = Results_1Compound_pine_only_thin[14]
                        R_PPulp[t]                  = Results_1Compound_pine_only_thin[15]
                        G_before                    = Results_1Compound_pine_only_thin[16]
                        R_BA                        = Results_1Compound_pine_only_thin[17]
                        ba[t]                       = Results_1Compound_pine_only_thin[18]
                        BGB[t]                      = Results_1Compound_pine_only_thin[19]
                        Tot_co2[t]                  = Results_1Compound_pine_only_thin[20]
                        Tot_biomass[t]              = Results_1Compound_pine_only_thin[21]
                        Total_carbon[t]             = Results_1Compound_pine_only_thin[22]
                        Tot_carbon_stems[t]         = Results_1Compound_pine_only_thin[23]
                        Tot_carbon_roots[t]         = Results_1Compound_pine_only_thin[24]
                        Tot_co2_stems[t]            = Results_1Compound_pine_only_thin[25]
                        Tot_co2_roots[t]            = Results_1Compound_pine_only_thin[26]
                                
                    else:
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        N_removed           = 0
                        R_vol_spruce        = R_vol_spruce
                        R_vol_birch         = R_vol_birch
                        R_vol_others        = R_vol_others
                        R_vol_ros           = R_vol_ros
                        R_vol_warm          = R_vol_warm
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]                       
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                                                 
            # (mic_t == "High_spruce") or (mic_t == "Medium_spruce")                     
            elif (Minor_species == "others_pine"): 
                for tree in trees:
                    t = tree                
                    if (t in trees_others) and (len(others_toDelete3) != 0): 
                        Results_1stCompound_others2_thin = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                     R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        N_removed                   = Results_1stCompound_others2_thin[0]
                        R_vol_birch                 = Results_1stCompound_others2_thin[1]
                        R_vol_others                = Results_1stCompound_others2_thin[2]
                        R_vol_ros                   = Results_1stCompound_others2_thin[3]
                        R_vol_warm                  = Results_1stCompound_others2_thin[4]
                        trees_dict[t]               = Results_1stCompound_others2_thin[5]
                        volsum[t]                   = Results_1stCompound_others2_thin[6]
                        vol_spruce[t]               = Results_1stCompound_others2_thin[7]
                        vol_pine[t]                 = Results_1stCompound_others2_thin[8]
                        vol_birch[t]                = Results_1stCompound_others2_thin[9]
                        vol_others[t]               = Results_1stCompound_others2_thin[10]
                        vol_ROS[t]                  = Results_1stCompound_others2_thin[11]
                        vol_warm[t]                 = Results_1stCompound_others2_thin[12]
                        R_SPulp[t]                  = Results_1stCompound_others2_thin[13]
                        R_SSaw[t]                   = Results_1stCompound_others2_thin[14]
                        R_HSaw[t]                   = Results_1stCompound_others2_thin[15]
                        R_HPulp[t]                  = Results_1stCompound_others2_thin[16]
                        R_PSaw[t]                   = Results_1stCompound_others2_thin[17]
                        R_PPulp[t]                  = Results_1stCompound_others2_thin[18]
                        G_before                    = Results_1stCompound_others2_thin[19]
                        R_BA                        = Results_1stCompound_others2_thin[20]
                        ba[t]                       = Results_1stCompound_others2_thin[21]
                        BGB[t]                      = Results_1stCompound_others2_thin[22]
                        Tot_co2[t]                  = Results_1stCompound_others2_thin[23]
                        Tot_biomass[t]              = Results_1stCompound_others2_thin[24]
                        Total_carbon[t]             = Results_1stCompound_others2_thin[25]
                        Tot_carbon_stems[t]         = Results_1stCompound_others2_thin[26]
                        Tot_carbon_roots[t]         = Results_1stCompound_others2_thin[27]
                        Tot_co2_stems[t]            = Results_1stCompound_others2_thin[28]
                        Tot_co2_roots[t]            = Results_1stCompound_others2_thin[29]
                        others_toDelete3.remove(str(t)) 
                            
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and len(others_toDelete3) == 0:                 
                        Results_2ndCompound_pine1_thin = self.Compound_pine_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                 Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                 N_removed, G_before)

                        N_removed                   = Results_2ndCompound_pine1_thin[0]
                        R_vol_spruce                = Results_2ndCompound_pine1_thin[1]
                        trees_dict[t]               = Results_2ndCompound_pine1_thin[2]
                        volsum[t]                   = Results_2ndCompound_pine1_thin[3]
                        vol_spruce[t]               = Results_2ndCompound_pine1_thin[4]
                        vol_pine[t]                 = Results_2ndCompound_pine1_thin[5]
                        vol_birch[t]                = Results_2ndCompound_pine1_thin[6]
                        vol_others[t]               = Results_2ndCompound_pine1_thin[7]
                        vol_ROS[t]                  = Results_2ndCompound_pine1_thin[8]
                        vol_warm[t]                 = Results_2ndCompound_pine1_thin[9]
                        R_SPulp[t]                  = Results_2ndCompound_pine1_thin[10]
                        R_SSaw[t]                   = Results_2ndCompound_pine1_thin[11]
                        R_HSaw[t]                   = Results_2ndCompound_pine1_thin[12]
                        R_HPulp[t]                  = Results_2ndCompound_pine1_thin[13]
                        R_PSaw[t]                   = Results_2ndCompound_pine1_thin[14]
                        R_PPulp[t]                  = Results_2ndCompound_pine1_thin[15]
                        G_before                    = Results_2ndCompound_pine1_thin[16]
                        R_BA                        = Results_2ndCompound_pine1_thin[17]
                        ba[t]                       = Results_2ndCompound_pine1_thin[18]
                        BGB[t]                      = Results_2ndCompound_pine1_thin[19]
                        Tot_co2[t]                  = Results_2ndCompound_pine1_thin[20]
                        Tot_biomass[t]              = Results_2ndCompound_pine1_thin[21]
                        Total_carbon[t]             = Results_2ndCompound_pine1_thin[22]
                        Tot_carbon_stems[t]         = Results_2ndCompound_pine1_thin[23]
                        Tot_carbon_roots[t]         = Results_2ndCompound_pine1_thin[24]
                        Tot_co2_stems[t]            = Results_2ndCompound_pine1_thin[25]
                        Tot_co2_roots[t]            = Results_2ndCompound_pine1_thin[26]
                        
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and len(others_toDelete3) == 0: 
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree 
                        N_removed           = 0
                        R_vol_spruce        = R_vol_spruce
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.  
                                               
            # (mic_t == "High_spruce") or (mic_t == "Medium_spruce")  
            elif (Minor_species == "pine_others_spruce"):
                for tree in trees:
                    t = tree                  
                    if (t in trees_pine) and (len(pine_toDelete3) !=0):                                     
                        Results_1stCompound_pine2_thin = self.firstCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                 Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine,
                                                                                 N_removed, G_before)
                        N_removed                  = Results_1stCompound_pine2_thin[0]
                        R_vol_pine                 = Results_1stCompound_pine2_thin[1]
                        trees_dict[t]              = Results_1stCompound_pine2_thin[2]
                        volsum[t]                  = Results_1stCompound_pine2_thin[3]
                        vol_spruce[t]              = Results_1stCompound_pine2_thin[4]
                        vol_pine[t]                = Results_1stCompound_pine2_thin[5]
                        vol_birch[t]               = Results_1stCompound_pine2_thin[6]
                        vol_others[t]              = Results_1stCompound_pine2_thin[7]
                        vol_ROS[t]                 = Results_1stCompound_pine2_thin[8]
                        vol_warm[t]                = Results_1stCompound_pine2_thin[9]
                        R_SPulp[t]                 = Results_1stCompound_pine2_thin[10]
                        R_SSaw[t]                  = Results_1stCompound_pine2_thin[11]
                        R_HSaw[t]                  = Results_1stCompound_pine2_thin[12]
                        R_HPulp[t]                 = Results_1stCompound_pine2_thin[13]
                        R_PSaw[t]                  = Results_1stCompound_pine2_thin[14]
                        R_PPulp[t]                 = Results_1stCompound_pine2_thin[15]
                        G_before                   = Results_1stCompound_pine2_thin[16]
                        R_BA                       = Results_1stCompound_pine2_thin[17]
                        ba[t]                      = Results_1stCompound_pine2_thin[18]
                        BGB[t]                     = Results_1stCompound_pine2_thin[19]
                        Tot_co2[t]                 = Results_1stCompound_pine2_thin[20]
                        Tot_biomass[t]             = Results_1stCompound_pine2_thin[21]
                        Total_carbon[t]            = Results_1stCompound_pine2_thin[22]
                        Tot_carbon_stems[t]        = Results_1stCompound_pine2_thin[23]
                        Tot_carbon_roots[t]        = Results_1stCompound_pine2_thin[24]
                        Tot_co2_stems[t]           = Results_1stCompound_pine2_thin[25]
                        Tot_co2_roots[t]           = Results_1stCompound_pine2_thin[26]
                        pine_toDelete3.remove(str(t))
                                                   
                for tree in trees:
                    t = tree
                    if (t in trees_others) and (len(pine_toDelete3) == 0) and (len(others_toDelete4) != 0):                                            
                        Results_MCompound_others2_thin = self.MiddleCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                    Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                    R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                        N_removed                   = Results_MCompound_others2_thin[0]
                        R_vol_birch                 = Results_MCompound_others2_thin[1]
                        R_vol_others                = Results_MCompound_others2_thin[2]
                        R_vol_ros                   = Results_MCompound_others2_thin[3]
                        R_vol_warm                  = Results_MCompound_others2_thin[4]
                        trees_dict[t]               = Results_MCompound_others2_thin[5]
                        volsum[t]                   = Results_MCompound_others2_thin[6]
                        vol_spruce[t]               = Results_MCompound_others2_thin[7]
                        vol_pine[t]                 = Results_MCompound_others2_thin[8]
                        vol_birch[t]                = Results_MCompound_others2_thin[9]
                        vol_others[t]               = Results_MCompound_others2_thin[10]
                        vol_ROS[t]                  = Results_MCompound_others2_thin[11]
                        vol_warm[t]                 = Results_MCompound_others2_thin[12]
                        R_SPulp[t]                  = Results_MCompound_others2_thin[13]
                        R_SSaw[t]                   = Results_MCompound_others2_thin[14]
                        R_HSaw[t]                   = Results_MCompound_others2_thin[15]
                        R_HPulp[t]                  = Results_MCompound_others2_thin[16]
                        R_PSaw[t]                   = Results_MCompound_others2_thin[17]
                        R_PPulp[t]                  = Results_MCompound_others2_thin[18]
                        G_before                    = Results_MCompound_others2_thin[19]
                        R_BA                        = Results_MCompound_others2_thin[20]
                        ba[t]                       = Results_MCompound_others2_thin[21]
                        BGB[t]                      = Results_MCompound_others2_thin[19]
                        Tot_co2[t]                  = Results_MCompound_others2_thin[20]
                        Tot_biomass[t]              = Results_MCompound_others2_thin[21]
                        Total_carbon[t]             = Results_MCompound_others2_thin[22]
                        Tot_carbon_stems[t]         = Results_MCompound_others2_thin[23]
                        Tot_carbon_roots[t]         = Results_MCompound_others2_thin[24]
                        Tot_co2_stems[t]            = Results_MCompound_others2_thin[25]
                        Tot_co2_roots[t]            = Results_MCompound_others2_thin[26]
                        others_toDelete4.remove(str(t)) 
                            
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and (len(others_toDelete4) == 0) and (len(pine_toDelete3) == 0):                    
                        Results_3rdCompound_Spruce1_thin = self.Compound_Spruce_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                     N_removed, G_before)
                        N_removed                   = Results_3rdCompound_Spruce1_thin[0]
                        R_vol_spruce                = Results_3rdCompound_Spruce1_thin[1]
                        trees_dict[t]               = Results_3rdCompound_Spruce1_thin[2]
                        volsum[t]                   = Results_3rdCompound_Spruce1_thin[3]
                        vol_spruce[t]               = Results_3rdCompound_Spruce1_thin[4]
                        vol_pine[t]                 = Results_3rdCompound_Spruce1_thin[5]
                        vol_birch[t]                = Results_3rdCompound_Spruce1_thin[6]
                        vol_others[t]               = Results_3rdCompound_Spruce1_thin[7]
                        vol_ROS[t]                  = Results_3rdCompound_Spruce1_thin[8]
                        vol_warm[t]                 = Results_3rdCompound_Spruce1_thin[9]
                        R_SPulp[t]                  = Results_3rdCompound_Spruce1_thin[10]
                        R_SSaw[t]                   = Results_3rdCompound_Spruce1_thin[11]
                        R_HSaw[t]                   = Results_3rdCompound_Spruce1_thin[12]
                        R_HPulp[t]                  = Results_3rdCompound_Spruce1_thin[13]
                        R_PSaw[t]                   = Results_3rdCompound_Spruce1_thin[14]
                        R_PPulp[t]                  = Results_3rdCompound_Spruce1_thin[15]
                        G_before                    = Results_3rdCompound_Spruce1_thin[16]
                        R_BA                        = Results_3rdCompound_Spruce1_thin[17]
                        ba[t]                       = Results_3rdCompound_Spruce1_thin[18]
                        BGB[t]                      = Results_3rdCompound_Spruce1_thin[19]
                        Tot_co2[t]                  = Results_3rdCompound_Spruce1_thin[20]
                        Tot_biomass[t]              = Results_3rdCompound_Spruce1_thin[21]
                        Total_carbon[t]             = Results_3rdCompound_Spruce1_thin[22]
                        Tot_carbon_stems[t]         = Results_3rdCompound_Spruce1_thin[23]
                        Tot_carbon_roots[t]         = Results_3rdCompound_Spruce1_thin[24]
                        Tot_co2_stems[t]            = Results_3rdCompound_Spruce1_thin[25]
                        Tot_co2_roots[t]            = Results_3rdCompound_Spruce1_thin[26]
        
            
        mgt = mgt    # this to specify that there is a management in this period
        for t in trees:
            if trees_dict[t] <= .00001:  
                trees_dict[t] = 0.
            #GrowthModel.GROWTH.append((R_SPulp[t],R_SSaw[t] ))
            
            attributes = dict(plot_id = self.DERIVED_TREES[t].plot_id,tree_id = self.DERIVED_TREES[t].tree_id,tree_sp = self.DERIVED_TREES[t].tree_sp, year = year, dbh = self.DERIVED_TREES[t].dbh , 
                              height = self.DERIVED_TREES[t].height, diameter_class = self.DERIVED_TREES[t].diameter_class, tree_Factor= self.DERIVED_TREES[t].tree_Factor , n_tree = trees_dict[t],
                              SI_spp = self.DERIVED_TREES[t].SI_spp, altitude_m = self.DERIVED_TREES[t].altitude_m, SI_m = self.DERIVED_TREES[t].SI_m, LAT = self.DERIVED_TREES[t].LAT, species = self.DERIVED_TREES[t].species, 
                              t_age =self.DERIVED_TREES[t].t_age , Period = period, yr_since_dead = self.DERIVED_TREES[t].yr_since_dead, Num_DeadTrees = self.DERIVED_TREES[t].Num_DeadTrees, Dom_species = self.DERIVED_TREES[t].Dom_species, BGB = BGB[t], 
                              Tot_co2 = Tot_co2[t], Total_carbon = Total_carbon[t], Tot_carbon_stems = Tot_carbon_stems[t] , Tot_carbon_roots = Tot_carbon_roots[t], 
                              Tot_co2_stems =Tot_co2_stems[t], Tot_co2_roots = Tot_co2_roots[t], Tot_biomass = Tot_biomass[t], vol_increment = self.DERIVED_TREES[t].vol_increment , 
                              dead_volume = self.DERIVED_TREES[t].dead_volume, dead_co2 = self.DERIVED_TREES[t].dead_co2, dead_biomass= self.DERIVED_TREES[t].dead_biomass, dead_C = self.DERIVED_TREES[t].dead_C, R_SPulp = R_SPulp[t], 
                              R_PPulp = R_PPulp[t], R_HPulp = R_HPulp[t], R_SSaw = R_SSaw[t] , R_PSaw = R_PSaw[t], R_HSaw = R_HSaw[t], Biomass_BAR = self.DERIVED_TREES[t].Biomass_BAR, Biomass_LGR = self.DERIVED_TREES[t].Biomass_LGR, 
                              Biomass_RGE5 = self.DERIVED_TREES[t].Biomass_RGE5, Biomass_RLT5= self.DERIVED_TREES[t].Biomass_RLT5, unwl = self.DERIVED_TREES[t].unwl, ufwl = self.DERIVED_TREES[t].ufwl, ucwl = self.DERIVED_TREES[t].ucwl , 
                              temp = self.DERIVED_TREES[t].temp, coord_x = self.DERIVED_TREES[t].coord_x, coord_y = self.DERIVED_TREES[t].coord_y, volsum = volsum[t], vol_spruce = vol_spruce[t], 
                              vol_pine = vol_pine[t], vol_birch = vol_birch[t], vol_others= vol_others[t] , vol_ROS = vol_ROS[t], vol_warm = vol_warm[t], ba = ba[t], management = mgt)
        
            GrowthModel.TreeGenerator(new_cls_name = t , new_parameters= attributes) 
                        
                                                        # %%%%%%     fR_CC     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    def fR_CC(self,R_BGB, R_co2, R_biomass, R_carbon, R_carbon_stems, R_carbon_roots, R_co2_stems, R_co2_roots, R_G, 
              Removed_trees, R_vol_tot, R_vol_spruce, R_vol_pine, R_vol_birch, R_vol_others, R_vol_ros, R_vol_warm,  
              G_b, G_left, mic_tp, year, period, mgt, **kwargs):
        
        """
        This function removes the objects which have met the conditions for clear cut and save small trees and broadleaves
        
        """
        Remove_BGB          =  R_BGB
        Remove_co2          =  R_co2
        Remove_biomass      =  R_biomass 
        Remove_carbon       =  R_carbon
        Remove_carbon_stems =  R_carbon_stems
        Remove_carbon_roots =  R_carbon_roots 
        Remove_co2_stems    =  R_co2_stems
        Remove_co2_roots    =  R_co2_roots
        
        N_removed    = Removed_trees 
        R_BA         = R_G
        R_vol_tot    = R_vol_tot
        R_vol_spruce = R_vol_spruce
        R_vol_pine   = R_vol_pine
        R_vol_birch  = R_vol_birch
        R_vol_others = R_vol_others
        R_vol_ros    = R_vol_ros 
        R_vol_warm   = R_vol_warm
        R_v_others     = R_vol_birch + R_vol_others + R_vol_ros + R_vol_warm
        
        allowed_diameter = 70
        BA_left = G_left
        G_before = G_b       
        mic_t = mic_tp
              
        trees_spruce, trees_pine, trees_others =[],[],[]
        trees_dict = collections.defaultdict(dict)
        R_SPulp = collections.defaultdict(dict)
        R_SSaw  = collections.defaultdict(dict)
        R_PPulp = collections.defaultdict(dict)
        R_PSaw  = collections.defaultdict(dict)
        R_HPulp = collections.defaultdict(dict)
        R_HSaw  = collections.defaultdict(dict)
        
        volsum  = collections.defaultdict(dict)
        vol_spruce  = collections.defaultdict(dict)
        vol_pine  = collections.defaultdict(dict)
        vol_birch  = collections.defaultdict(dict)
        vol_others  = collections.defaultdict(dict)
        vol_ROS  = collections.defaultdict(dict)
        vol_warm  = collections.defaultdict(dict)
        
        BGB                = collections.defaultdict(dict)
        Tot_co2            = collections.defaultdict(dict)
        Tot_biomass        = collections.defaultdict(dict)
        Total_carbon       = collections.defaultdict(dict)
        Tot_carbon_stems   = collections.defaultdict(dict)
        Tot_carbon_roots   = collections.defaultdict(dict)
        Tot_co2_stems      = collections.defaultdict(dict)
        Tot_co2_roots      = collections.defaultdict(dict)
        
        ba = collections.defaultdict(dict)
                
               
        # This part will determine the the minority species for cutting
        trees = set([k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0])
        
        V_sum = sum([(self.DERIVED_TREES[k].volsum + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys()])
        V_spruce = sum([(self.DERIVED_TREES[k].vol_spruce + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_pine = sum([(self.DERIVED_TREES[k].vol_pine + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_birch = sum([(self.DERIVED_TREES[k].vol_birch + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])  
        V_other = sum([(self.DERIVED_TREES[k].vol_others + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_ROS = sum([(self.DERIVED_TREES[k].vol_ROS + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_warm =  sum([(self.DERIVED_TREES[k].vol_warm + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])        
        
        V_others = V_birch + V_other + V_ROS + V_warm
        
        print(R_vol_tot, V_spruce, V_pine, V_others)

        # N_spruce = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "spruce" ])
        # N_pine = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "scots_pine" ])
        # N_birch = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "birch" ]) 
        # N_other = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "other_broadleaves" ])
        # N_ROS = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "ROS" ])
        # N_warm =  sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "warm"])        

        # N_others = N_birch + N_other + N_ROS + N_warm

                
        for k in trees:
            if GrowthModel.DERIVED_TREES[k].dbh >= allowed_diameter:
                if GrowthModel.DERIVED_TREES[k].species == "spruce" :
                    trees_spruce.append(k)                
                elif GrowthModel.DERIVED_TREES[k].species == "scots_pine" :
                    trees_pine.append(k)                    
                elif (GrowthModel.DERIVED_TREES[k].species == "birch") :
                    trees_others.append(k)
                elif (GrowthModel.DERIVED_TREES[k].species == "other_broadleaves") :
                    trees_others.append(k)
                elif (GrowthModel.DERIVED_TREES[k].species == "ROS") :
                    trees_others.append(k)
                elif (GrowthModel.DERIVED_TREES[k].species == "warm") :
                    trees_others.append(k)
        
        Scenario_spruce_CC       = ["spruce_pine", "pine_spruce", "pine_only", "spruce_only", "spruce_pine_others", "spruce_others", "others_spruce", "spruce_others_pine", "others_pine", "pine_others"]
        Scenario_pine_CC         = ["spruce_some", "spruce_pine", "spruce_only", "spruce_others_pine", "others_pine", "others_only", "spruce_others", "others_spruce", "pine_only"]
        Scenario_broadleaves_CC  = ["others_spruce", "spruce_others", "others_only", "others_pine", "pine_others", "others_pine_spruce", "others_spruce_pine"]
        # this part difines which trees should (not) be cut
        CutFirst = ""
        if (mic_t == "High_spruce") or (mic_t == "Medium_spruce") or (mic_t == "Low_spruce"):
   
            if R_vol_tot <= (V_pine + V_spruce) and (V_others == 0): # case1

                if (R_vol_tot > V_pine) and (R_vol_tot > V_spruce) and (V_pine < V_spruce):
                    CutFirst = Scenario_spruce_CC[1]
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_spruce) and (V_pine >= V_spruce):
                    CutFirst = Scenario_spruce_CC[1]             
                    
                elif (R_vol_tot > V_pine) and (R_vol_tot < V_spruce) and (V_spruce > V_pine ):
                     CutFirst = Scenario_spruce_CC[1] 
                     
                elif (R_vol_tot == V_pine) :
                    CutFirst = Scenario_spruce_CC[2]
                elif (R_vol_tot == V_spruce) and (V_pine == 0):
                    CutFirst = Scenario_spruce_CC[3]
                elif (R_vol_tot > V_spruce) and (R_vol_tot != V_pine) and (V_spruce <= V_pine):
                    CutFirst = Scenario_spruce_CC[1]
                elif (R_vol_tot > V_pine) and (R_vol_tot != V_spruce) and (V_pine <= V_spruce):
                    CutFirst = Scenario_spruce_CC[1]
                    
            elif R_vol_tot <= (V_others + V_spruce) and (V_pine == 0): # case2

                if (R_vol_tot >= V_others) and (R_vol_tot > V_spruce) and (V_others < V_spruce) and (V_others != 0):
                    CutFirst = Scenario_spruce_CC[5] #"spruce_others"
                
                elif (R_vol_tot > V_others) and (R_vol_tot > V_spruce) and (V_others > V_spruce) and (V_others != 0):
                    CutFirst = Scenario_spruce_CC[6] #"others_spruce"
                    
                elif (R_vol_tot > V_others) and (R_vol_tot > V_spruce) and (V_others >= V_spruce) and (V_others != 0):
                    CutFirst = Scenario_spruce_CC[6] 
                
                elif (R_vol_tot > V_others) and (R_vol_tot > V_spruce) and (V_spruce > V_others ) and (V_others != 0):
                    CutFirst = Scenario_spruce_CC[5]                    
                    
                elif (R_vol_tot > V_others) and (R_vol_tot < V_spruce) and (V_others != 0):
                     CutFirst = Scenario_spruce_CC[6] 
                
                elif (R_vol_tot == V_spruce) and (V_pine == 0) and (V_others == 0):
                    CutFirst = Scenario_spruce_CC[3]
                
                elif (R_vol_tot > V_spruce) and (R_vol_tot != V_others) and (V_spruce <= V_others):
                    CutFirst = Scenario_spruce_CC[5]
                
                elif (R_vol_tot > V_others) and (R_vol_tot != V_spruce) and (V_others <= V_spruce) and (V_others != 0):
                    CutFirst = Scenario_spruce_CC[6]
        

            elif R_vol_tot <= (V_pine + V_spruce) and (V_pine > V_others): # case3
                CutFirst = Scenario_spruce_CC[1]
                
            elif R_vol_tot <= (V_pine + V_spruce) and (V_pine < V_others): # case3-1
                CutFirst = Scenario_spruce_CC[6]
            
            elif R_vol_tot > (V_pine + V_spruce) and (V_pine != 0) and (V_others != 0): # case5

                CutFirst = Scenario_spruce_CC[4]
                
            elif R_vol_tot > (V_others + V_spruce) and (V_pine != 0) and (V_others != 0): # case5
 
                CutFirst = Scenario_spruce_CC[4]
                
            elif R_vol_tot > (V_pine + V_spruce + V_others) and V_pine == 0 and (V_others == 0):  # case6
 
                CutFirst = Scenario_spruce_CC[3]
                
            elif R_vol_tot <= (V_pine + V_spruce + V_others) and (V_pine < V_others) and V_pine != 0:  # case4

                CutFirst = Scenario_spruce_CC[7]
                
            elif R_vol_tot <= (V_pine + V_spruce + V_others):  # case4

                if (R_vol_tot <= V_others + V_spruce) and (R_vol_tot >= V_others) and (R_vol_tot >= V_spruce)  and (V_pine < V_spruce) and (V_pine < V_others) and (V_spruce >= V_others):
                    CutFirst = Scenario_spruce_CC[5]   #"spruce_others"
                elif (R_vol_tot <= V_others + V_spruce) and (R_vol_tot >= V_others) and (R_vol_tot >= V_spruce) and (V_pine <= V_spruce) and (V_pine <= V_others) and (V_others >= V_spruce):
                    CutFirst = Scenario_spruce_CC[6]  #"others_spruce"
                
                elif (R_vol_tot <= V_others + V_spruce) and (R_vol_tot >= V_others) and (R_vol_tot >= V_spruce) and (V_pine >= V_spruce) and (V_pine >= V_others) and (V_others <= V_spruce):
                    CutFirst = Scenario_spruce_CC[1]  #pine_spruce"
                            
                elif (R_vol_tot <= V_pine + V_spruce) and (R_vol_tot >= V_pine) and (R_vol_tot >= V_spruce)  and (V_pine < V_spruce) and (V_pine < V_others) and (V_spruce >= V_others):
                    CutFirst = Scenario_spruce_CC[5]  #"spruce_others"
                         
                elif (R_vol_tot <= V_pine + V_spruce) and (R_vol_tot >= V_spruce) and (R_vol_tot >= V_pine) and (V_pine >= V_spruce) and (V_spruce >= V_others):
                    CutFirst = Scenario_spruce_CC[1] #"pine_spruce"
                
                elif (R_vol_tot <= V_pine + V_spruce) and (R_vol_tot >= V_pine) and (V_pine <= V_spruce) and (V_pine >= V_others) and (V_spruce >= V_others):
                    CutFirst = Scenario_spruce_CC[0] #"spruce_pine"
                
                elif (R_vol_tot >= V_others + V_spruce) and (R_vol_tot <= V_pine + V_spruce) and (R_vol_tot >= V_pine) and (V_pine <= V_spruce) and (V_pine >= V_others) and (V_spruce >= V_others):
                    CutFirst = Scenario_spruce_CC[0]
                                  
                elif (R_vol_tot >= V_pine + V_spruce) and (R_vol_tot <= V_others + V_spruce) and (R_vol_tot >= V_others) and (V_pine <= V_spruce) and (V_pine <= V_others) and (V_spruce >= V_others):
                    CutFirst = Scenario_spruce_CC[5]
                    
                elif (R_vol_tot >= V_pine + V_spruce) and (R_vol_tot <= V_others + V_spruce) and (R_vol_tot >= V_others) and (V_pine <= V_spruce) and (V_pine <= V_others) and (V_spruce <= V_others):
                    CutFirst = Scenario_spruce_CC[6]
                
                elif (R_vol_tot <= V_pine + V_others) and (R_vol_tot >= V_others + V_spruce) and (V_pine >= V_spruce) and (V_pine <= V_others) and (V_spruce <= V_others):
                    CutFirst = Scenario_spruce_CC[8] # "others_pine"
                    
                elif (R_vol_tot <= V_pine + V_others) and (R_vol_tot <= V_pine + V_spruce)  and (V_pine >= V_spruce) and (V_pine >= V_others) and (V_spruce <= V_others):
                    CutFirst = Scenario_spruce_CC[9]  # "pine_others"
                
                elif (R_vol_tot <= V_others + V_pine) and (R_vol_tot >= V_others) and (R_vol_tot >= V_spruce) and (V_pine >= V_spruce) and (V_pine <= V_others) and (V_others >= V_spruce):
                    CutFirst = Scenario_spruce_CC[8]  # "others_pine"
                    
                elif (R_vol_tot <= V_others + V_pine) and (R_vol_tot >= V_others) and (R_vol_tot >= V_pine) and (V_pine >= V_spruce) and (V_pine >= V_others) and (V_others >= V_spruce):
                    CutFirst = Scenario_spruce_CC[9]  # "pine_others"
                    
                elif (R_vol_tot <= V_spruce) and (V_pine == 0) and (V_others == 0):
                    CutFirst = Scenario_spruce_CC[3]
                
                elif (R_vol_tot <= V_spruce) and (R_vol_tot <= V_others) and (V_pine == 0):
                    CutFirst = Scenario_spruce_CC[3]                
                
                    
        elif (mic_t == "High_pine"):
            
            if R_vol_tot <= (V_spruce + V_pine) and (V_others == 0) and (V_spruce != 0): # case1
                
                if (R_vol_tot <= V_pine) and (R_vol_tot < V_spruce) and (V_pine < V_spruce) and (R_vol_tot != V_spruce):
                    CutFirst = Scenario_pine_CC[0]
                elif (R_vol_tot < V_pine) and (R_vol_tot < V_spruce) and (V_pine > V_spruce) and (R_vol_tot != V_spruce):
                    CutFirst = Scenario_pine_CC[0]
                
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_spruce) and (V_pine >= V_spruce) and (V_pine != 0):
                    CutFirst = Scenario_pine_CC[1]
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_spruce) and (V_spruce > V_pine ) and (V_pine != 0):
                    CutFirst = Scenario_pine_CC[1]   
                    
                elif (R_vol_tot < V_pine) and (R_vol_tot > V_spruce):
                     CutFirst = Scenario_pine_CC[1]
                elif (R_vol_tot > V_pine) and (R_vol_tot < V_spruce):
                     CutFirst = Scenario_pine_CC[0] 
                elif (R_vol_tot == V_pine) and (R_vol_tot > V_spruce) and (V_pine != 0):
                    CutFirst = Scenario_pine_CC[1]
                elif (R_vol_tot == V_spruce) and (R_vol_tot >= V_pine):
                    CutFirst = Scenario_pine_CC[2]
                elif (R_vol_tot > V_spruce) and (R_vol_tot != V_pine) and (V_spruce <= V_pine) and (V_pine != 0):
                    CutFirst = Scenario_pine_CC[1]
                elif (R_vol_tot > V_pine) and (R_vol_tot != V_spruce) and (V_pine <= V_spruce) and (V_pine != 0):
                    CutFirst = Scenario_pine_CC[1]
                    
            elif R_vol_tot <= (V_others + V_pine) and (V_spruce== 0) and (V_others != 0): # case2
                
                if (R_vol_tot <= V_pine) and (R_vol_tot < V_others) and (V_pine < V_others):
                    CutFirst = Scenario_pine_CC[5]
                elif (R_vol_tot < V_pine) and (R_vol_tot < V_others) and (V_pine > V_others):
                    CutFirst = Scenario_pine_CC[5]
                
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_others) and (V_pine >= V_others) and (V_pine != 0):
                    CutFirst = Scenario_pine_CC[4]
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_others) and (V_others > V_pine ) and (V_pine != 0):
                    CutFirst = Scenario_pine_CC[4] 
                    
                elif (R_vol_tot < V_pine) and (R_vol_tot > V_others):
                     CutFirst = Scenario_pine_CC[4]
                elif (R_vol_tot > V_pine) and (R_vol_tot < V_others):
                     CutFirst = Scenario_pine_CC[5]
            
            elif R_vol_tot <= (V_others + V_spruce) and (V_spruce != 0)  and (V_others != 0): # case3
                
                if (R_vol_tot > V_spruce) and (R_vol_tot > V_others) and (V_spruce >= V_others):
                    CutFirst = Scenario_pine_CC[6]
                elif (R_vol_tot > V_spruce) and (R_vol_tot > V_others) and (V_others > V_spruce ):
                    CutFirst = Scenario_pine_CC[7]
                    
            elif R_vol_tot <= (V_spruce + V_others + V_pine) and (V_spruce == 0)  and (V_others == 0): # case4
                CutFirst = Scenario_pine_CC[8]
            
            elif R_vol_tot > (V_spruce + V_others) and (V_spruce != 0)  and (V_others != 0): # case5
                CutFirst = Scenario_pine_CC[3] 
            
            elif R_vol_tot > (V_spruce + V_others) and (V_spruce == 0)  and (V_others != 0): # case6
                CutFirst = Scenario_pine_CC[4]
            
                
        elif (mic_t == "broadleaf"):
            if R_vol_tot <= (V_spruce + V_others) and V_spruce != 0 : # case1
                if (R_vol_tot > V_others) and (R_vol_tot > V_spruce) and (V_others > V_spruce):
                    CutFirst = Scenario_broadleaves_CC[0] #ok
                elif (R_vol_tot > V_others) and (R_vol_tot > V_spruce) and (V_spruce > V_others):
                    CutFirst = Scenario_broadleaves_CC[1] #ok
                elif (R_vol_tot <= V_others): 
                    CutFirst = Scenario_broadleaves_CC[2]
            
            elif R_vol_tot <= (V_pine + V_others) and V_pine != 0: # case2
                
                if (R_vol_tot > V_others) and (R_vol_tot > V_pine) and (V_others > V_pine): #ok
                    CutFirst = Scenario_broadleaves_CC[3]
                elif (R_vol_tot > V_others) and (R_vol_tot > V_pine) and (V_pine > V_others) and (R_vol_tot != V_pine):
                    CutFirst = Scenario_broadleaves_CC[4]
                elif (R_vol_tot <= V_others): 
                    CutFirst = Scenario_broadleaves_CC[2]
            
            elif R_vol_tot <= V_others and V_pine == 0 and V_spruce == 0: # case4
                CutFirst = Scenario_broadleaves_CC[2]
                
            elif R_vol_tot > (V_spruce + V_others) and V_spruce != 0 and (V_others > V_spruce) and (V_others > V_pine ) and (V_pine > V_spruce):
                CutFirst = Scenario_broadleaves_CC[5]
            elif R_vol_tot > (V_spruce + V_others) and V_spruce != 0 and (V_others > V_spruce) and (V_others > V_pine ) and (V_spruce > V_pine):  
                CutFirst = Scenario_broadleaves_CC[6]
            elif R_vol_tot > (V_pine + V_others) and V_pine != 0 and (V_others > V_spruce) and (V_others > V_pine ) and (V_pine > V_spruce):
                CutFirst = Scenario_broadleaves_CC[5]
            elif R_vol_tot > (V_spruce + V_others) and V_spruce != 0 and (V_others < V_spruce) and (V_others > V_pine ) and (V_pine < V_spruce):
                CutFirst = Scenario_broadleaves_CC[6]
            elif R_vol_tot > (V_spruce + V_others) and V_spruce != 0 and (V_others < V_spruce) and (V_others > V_pine ) and (V_pine > V_spruce):
                CutFirst = Scenario_broadleaves_CC[5]
            elif R_vol_tot > (V_spruce + V_others) and V_spruce != 0 and (V_others < V_spruce) and (V_others < V_pine ) and (V_pine > V_spruce):
                CutFirst = Scenario_broadleaves_CC[5]
            elif R_vol_tot > (V_spruce + V_others) and V_spruce != 0 and (V_others < V_spruce) and (V_others < V_pine ) and (V_pine < V_spruce):
                CutFirst = Scenario_broadleaves_CC[6]
                
          
        # this list will be used for updating the objects
        
        trees_spruce_toDelete1 = trees_spruce.copy()
        trees_spruce_toDelete2 = trees_spruce.copy()
        trees_spruce_toDelete3 = trees_spruce.copy()
        trees_spruce_toDelete4 = trees_spruce.copy()
        trees_spruce_toDelete8 = trees_spruce.copy()
        trees_pine_toDelete1 = trees_pine.copy()
        trees_pine_toDelete2 = trees_pine.copy()
        trees_pine_toDelete3 = trees_pine.copy()
        trees_pine_toDelete4 = trees_pine.copy()
        trees_pine1_toDelete = trees_pine.copy()
        
        trees_others_s1_toDelete = trees_others.copy()
        trees_others_s2_toDelete = trees_others.copy()
        trees_others_s3_toDelete = trees_others.copy()
        trees_others_s4_toDelete = trees_others.copy()
        trees_others_s5_toDelete = trees_others.copy()
        trees_others_s6_toDelete = trees_others.copy()
        trees_others_s7_toDelete = trees_others.copy()
        trees_others_s9_toDelete = trees_others.copy()
        
        trees_others_p1_toDelete = trees_others.copy()
        trees_others_p2_toDelete = trees_others.copy()
        trees_others_p3_toDelete = trees_others.copy()
        trees_others_p4_toDelete = trees_others.copy()
        trees_others_p5_toDelete = trees_others.copy()
        
        trees_spruce_toDelete5 = trees_spruce.copy()
        trees_spruce_toDelete6 = trees_spruce.copy()
        trees_spruce_toDelete7 = trees_spruce.copy()
        trees_spruce1_toDelete = trees_spruce.copy()
        
        if (mic_t == "High_pine"):
            if (CutFirst ==  "spruce_pine"):
                for tree in trees:
                    t= tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and (len(trees_spruce_toDelete1) != 0): 
                            Results_1stCompound_spruce1_CC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                       N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce1_CC[0]
                            R_vol_spruce               = Results_1stCompound_spruce1_CC[1]
                            trees_dict[t]              = Results_1stCompound_spruce1_CC[2]
                            volsum[t]                  = Results_1stCompound_spruce1_CC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce1_CC[4] 
                            vol_pine[t]                = Results_1stCompound_spruce1_CC[5]
                            vol_birch[t]               = Results_1stCompound_spruce1_CC[6]
                            vol_others[t]              = Results_1stCompound_spruce1_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce1_CC[8]
                            vol_warm[t]                = Results_1stCompound_spruce1_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce1_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce1_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce1_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce1_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce1_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce1_CC[15]
                            G_before                   = Results_1stCompound_spruce1_CC[16]
                            R_BA                       = Results_1stCompound_spruce1_CC[17]
                            ba[t]                      = Results_1stCompound_spruce1_CC[18]
                            BGB[t]                     = Results_1stCompound_spruce1_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce1_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce1_CC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce1_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce1_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce1_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce1_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce1_CC[26]
                            trees_spruce_toDelete1.remove(str(t))
                        
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine)  and len(trees_spruce_toDelete1) == 0: 
                            Results_2ndCompound_pine4_CC = self.LastCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                  Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine, 
                                                                                  N_removed, G_before)
                            N_removed               = Results_2ndCompound_pine4_CC[0]
                            R_vol_pine              = Results_2ndCompound_pine4_CC[1]
                            trees_dict[t]           = Results_2ndCompound_pine4_CC[2]
                            volsum[t]               = Results_2ndCompound_pine4_CC[3]
                            vol_spruce[t]           = Results_2ndCompound_pine4_CC[4]
                            vol_pine[t]             = Results_2ndCompound_pine4_CC[5]
                            vol_birch[t]            = Results_2ndCompound_pine4_CC[6]
                            vol_others[t]           = Results_2ndCompound_pine4_CC[7]
                            vol_ROS[t]              = Results_2ndCompound_pine4_CC[8]
                            vol_warm[t]             = Results_2ndCompound_pine4_CC[9]
                            R_SPulp[t]              = Results_2ndCompound_pine4_CC[10]
                            R_SSaw[t]               = Results_2ndCompound_pine4_CC[11]
                            R_HSaw[t]               = Results_2ndCompound_pine4_CC[12]
                            R_HPulp[t]              = Results_2ndCompound_pine4_CC[13]
                            R_PSaw[t]               = Results_2ndCompound_pine4_CC[14]
                            R_PPulp[t]              = Results_2ndCompound_pine4_CC[15]
                            G_before                = Results_2ndCompound_pine4_CC[16]
                            R_BA                    = Results_2ndCompound_pine4_CC[17]
                            ba[t]                   = Results_2ndCompound_pine4_CC[18]
                            BGB[t]                  = Results_2ndCompound_pine4_CC[19]
                            Tot_co2[t]              = Results_2ndCompound_pine4_CC[20]
                            Tot_biomass[t]          = Results_2ndCompound_pine4_CC[21]
                            Total_carbon[t]         = Results_2ndCompound_pine4_CC[22]
                            Tot_carbon_stems[t]     = Results_2ndCompound_pine4_CC[23]
                            Tot_carbon_roots[t]     = Results_2ndCompound_pine4_CC[24]
                            Tot_co2_stems[t]        = Results_2ndCompound_pine4_CC[25]
                            Tot_co2_roots[t]        = Results_2ndCompound_pine4_CC[26]
    
                    else:
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        R_vol_spruce        = R_vol_spruce
                        R_vol_pine          = R_vol_pine
                        R_vol_birch         = R_vol_birch
                        R_vol_others        = R_vol_others
                        R_vol_ros           = R_vol_ros
                        R_vol_warm          = R_vol_warm
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0. 

                                
                for t in trees:
                    if (t in trees_others)  and (len(trees_spruce_toDelete1) == 0): 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 
            
            ##mic_t == "High_pine" 
            elif CutFirst == "others_only":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_others:
                            Results_Compound_others1_only_CC = self.SecondCompound_Others(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                         R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)                           
                            N_removed                   = Results_Compound_others1_only_CC[0]
                            R_vol_birch                 = Results_Compound_others1_only_CC[1]
                            R_vol_others                = Results_Compound_others1_only_CC[2]
                            R_vol_ros                   = Results_Compound_others1_only_CC[3]
                            R_vol_warm                  = Results_Compound_others1_only_CC[4]
                            trees_dict[t]               = Results_Compound_others1_only_CC[5]
                            volsum[t]                   = Results_Compound_others1_only_CC[6]
                            vol_spruce[t]               = Results_Compound_others1_only_CC[7]
                            vol_pine[t]                 = Results_Compound_others1_only_CC[8]
                            vol_birch[t]                = Results_Compound_others1_only_CC[9]
                            vol_others[t]               = Results_Compound_others1_only_CC[10]
                            vol_ROS[t]                  = Results_Compound_others1_only_CC[11]
                            vol_warm[t]                 = Results_Compound_others1_only_CC[12]
                            R_SPulp[t]                  = Results_Compound_others1_only_CC[13]
                            R_SSaw[t]                   = Results_Compound_others1_only_CC[14]
                            R_HSaw[t]                   = Results_Compound_others1_only_CC[15]
                            R_HPulp[t]                  = Results_Compound_others1_only_CC[16]
                            R_PSaw[t]                   = Results_Compound_others1_only_CC[17]
                            R_PPulp[t]                  = Results_Compound_others1_only_CC[18]
                            G_before                    = Results_Compound_others1_only_CC[19]
                            R_BA                        = Results_Compound_others1_only_CC[20]
                            ba[t]                       = Results_Compound_others1_only_CC[21]
                            BGB[t]                      = Results_Compound_others1_only_CC[22]
                            Tot_co2[t]                  = Results_Compound_others1_only_CC[23]
                            Tot_biomass[t]              = Results_Compound_others1_only_CC[24]
                            Total_carbon[t]             = Results_Compound_others1_only_CC[25]
                            Tot_carbon_stems[t]         = Results_Compound_others1_only_CC[26]
                            Tot_carbon_roots[t]         = Results_Compound_others1_only_CC[27]
                            Tot_co2_stems[t]            = Results_Compound_others1_only_CC[28]
                            Tot_co2_roots[t]            = Results_Compound_others1_only_CC[29]
                                                                      
                        else:
                            n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t]       = n_tree
                            N_removed           = 0
                            R_vol_spruce        = R_vol_spruce
                            R_vol_pine          = R_vol_pine
                            G_before            = G_before
                            R_BA                = R_BA
                            ba[t]               = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                            volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]           = 0.
                            R_HPulp[t]          = 0.
                            R_PSaw[t]           = 0.
                            R_PPulp[t]          = 0. 
                            R_SSaw[t]           = 0.
                            R_SPulp[t]          = 0.
                            
                    else:
                        n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t]       = n_tree
                        N_removed           = 0
                        R_vol_spruce        = R_vol_spruce
                        R_vol_pine          = R_vol_pine
                        R_vol_birch         = R_vol_birch
                        R_vol_others        = R_vol_others
                        R_vol_ros           = R_vol_ros
                        R_vol_warm          = R_vol_warm
                        G_before            = G_before
                        R_BA                = R_BA
                        ba[t]               = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]           = 0.
                        R_PPulp[t]          = 0.
                        R_HSaw[t]           = 0.
                        R_HPulp[t]          = 0.
                        R_SSaw[t]           = 0.
                        R_SPulp[t]          = 0.        
            
            ##mic_t == "High_pine"                                         
            elif CutFirst == "others_pine":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):                        
                        if (t in trees_others) and (len(trees_others_p2_toDelete) != 0):    
                            Results_1stCompound_others1_CC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed               = Results_1stCompound_others1_CC[0]
                            R_vol_birch             = Results_1stCompound_others1_CC[1]
                            R_vol_others            = Results_1stCompound_others1_CC[2]
                            R_vol_ros               = Results_1stCompound_others1_CC[3]
                            R_vol_warm              = Results_1stCompound_others1_CC[4]
                            trees_dict[t]           = Results_1stCompound_others1_CC[5]
                            volsum[t]               = Results_1stCompound_others1_CC[6]
                            vol_spruce[t]           = Results_1stCompound_others1_CC[7]
                            vol_pine[t]             = Results_1stCompound_others1_CC[8]
                            vol_birch[t]            = Results_1stCompound_others1_CC[9]
                            vol_others[t]           = Results_1stCompound_others1_CC[10]
                            vol_ROS[t]              = Results_1stCompound_others1_CC[11]
                            vol_warm[t]             = Results_1stCompound_others1_CC[12]
                            R_SPulp[t]              = Results_1stCompound_others1_CC[13]
                            R_SSaw[t]               = Results_1stCompound_others1_CC[14]
                            R_HSaw[t]               = Results_1stCompound_others1_CC[15]
                            R_HPulp[t]              = Results_1stCompound_others1_CC[16]
                            R_PSaw[t]               = Results_1stCompound_others1_CC[17]
                            R_PPulp[t]              = Results_1stCompound_others1_CC[18]
                            G_before                = Results_1stCompound_others1_CC[19]
                            R_BA                    = Results_1stCompound_others1_CC[20]
                            ba[t]                   = Results_1stCompound_others1_CC[21]
                            BGB[t]                  = Results_1stCompound_others1_CC[22]
                            Tot_co2[t]              = Results_1stCompound_others1_CC[23]
                            Tot_biomass[t]          = Results_1stCompound_others1_CC[24]
                            Total_carbon[t]         = Results_1stCompound_others1_CC[25]
                            Tot_carbon_stems[t]     = Results_1stCompound_others1_CC[26]
                            Tot_carbon_roots[t]     = Results_1stCompound_others1_CC[27]
                            Tot_co2_stems[t]        = Results_1stCompound_others1_CC[28]
                            Tot_co2_roots[t]        = Results_1stCompound_others1_CC[29]
                            trees_others_p2_toDelete.remove(str(t))
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                                
                for tree in trees:
                    t = tree   
                    if (G_before > BA_left):
                        if (t in trees_pine) and len(trees_others_p2_toDelete) == 0:
                            Results_2ndCompound_pine1_CC = self.Compound_pine_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                   N_removed, G_before)
                            N_removed               = Results_2ndCompound_pine1_CC[0]
                            R_vol_pine              = Results_2ndCompound_pine1_CC[1]
                            trees_dict[t]           = Results_2ndCompound_pine1_CC[2]
                            volsum[t]               = Results_2ndCompound_pine1_CC[3]
                            vol_spruce[t]           = Results_2ndCompound_pine1_CC[4]
                            vol_pine[t]             = Results_2ndCompound_pine1_CC[5]
                            vol_birch[t]            = Results_2ndCompound_pine1_CC[6]
                            vol_others[t]           = Results_2ndCompound_pine1_CC[7]
                            vol_ROS[t]              = Results_2ndCompound_pine1_CC[8]
                            vol_warm[t]             = Results_2ndCompound_pine1_CC[9]
                            R_SPulp[t]              = Results_2ndCompound_pine1_CC[10]
                            R_SSaw[t]               = Results_2ndCompound_pine1_CC[11]
                            R_HSaw[t]               = Results_2ndCompound_pine1_CC[12]
                            R_HPulp[t]              = Results_2ndCompound_pine1_CC[13]
                            R_PSaw[t]               = Results_2ndCompound_pine1_CC[14]
                            R_PPulp[t]              = Results_2ndCompound_pine1_CC[15]
                            G_before                = Results_2ndCompound_pine1_CC[16]
                            R_BA                    = Results_2ndCompound_pine1_CC[17]
                            ba[t]                   = Results_2ndCompound_pine1_CC[18]
                            BGB[t]                  = Results_2ndCompound_pine1_CC[19]
                            Tot_co2[t]              = Results_2ndCompound_pine1_CC[20]
                            Tot_biomass[t]          = Results_2ndCompound_pine1_CC[21]
                            Total_carbon[t]         = Results_2ndCompound_pine1_CC[22]
                            Tot_carbon_stems[t]     = Results_2ndCompound_pine1_CC[23]
                            Tot_carbon_roots[t]     = Results_2ndCompound_pine1_CC[24]
                            Tot_co2_stems[t]        = Results_2ndCompound_pine1_CC[25]
                            Tot_co2_roots[t]        = Results_2ndCompound_pine1_CC[26]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                            
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and len(trees_others_p2_toDelete) == 0: 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree 
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.  

                                                           
            elif CutFirst ==  "spruce_some":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_spruce:
                            Results_Compound_Spruce1_CC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                    Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                    N_removed, G_before)
                            N_removed               = Results_Compound_Spruce1_CC[0]
                            R_vol_spruce            = Results_Compound_Spruce1_CC[1]
                            trees_dict[t]           = Results_Compound_Spruce1_CC[2]
                            volsum[t]               = Results_Compound_Spruce1_CC[3]
                            vol_spruce[t]           = Results_Compound_Spruce1_CC[4]
                            vol_pine[t]             = Results_Compound_Spruce1_CC[5]
                            vol_birch[t]            = Results_Compound_Spruce1_CC[6]
                            vol_others[t]           = Results_Compound_Spruce1_CC[7]
                            vol_ROS[t]              = Results_Compound_Spruce1_CC[8]
                            vol_warm[t]             = Results_Compound_Spruce1_CC[9]
                            R_SPulp[t]              = Results_Compound_Spruce1_CC[10]
                            R_SSaw[t]               = Results_Compound_Spruce1_CC[11]
                            R_HSaw[t]               = Results_Compound_Spruce1_CC[12]
                            R_HPulp[t]              = Results_Compound_Spruce1_CC[13]
                            R_PSaw[t]               = Results_Compound_Spruce1_CC[14]
                            R_PPulp[t]              = Results_Compound_Spruce1_CC[15]
                            G_before                = Results_Compound_Spruce1_CC[16]
                            R_BA                    = Results_Compound_Spruce1_CC[17]
                            ba[t]                   = Results_Compound_Spruce1_CC[18]
                            BGB[t]                  = Results_Compound_Spruce1_CC[19]
                            Tot_co2[t]              = Results_Compound_Spruce1_CC[20]
                            Tot_biomass[t]          = Results_Compound_Spruce1_CC[21]
                            Total_carbon[t]         = Results_Compound_Spruce1_CC[22]
                            Tot_carbon_stems[t]     = Results_Compound_Spruce1_CC[23]
                            Tot_carbon_roots[t]     = Results_Compound_Spruce1_CC[24]
                            Tot_co2_stems[t]        = Results_Compound_Spruce1_CC[25]
                            Tot_co2_roots[t]        = Results_Compound_Spruce1_CC[26]

                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree 
                            N_removed     = 0
                            R_vol_pine    = R_vol_pine
                            R_vol_birch   = R_vol_birch
                            R_vol_others  = R_vol_others
                            R_vol_ros     = R_vol_ros
                            R_vol_warm    = R_vol_warm
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0.
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
            
            #mic_t == "High_pine"
            elif (CutFirst ==  "spruce_only"):
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_spruce:
                            Results_Compound_Spruce1_only_CC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed               = Results_Compound_Spruce1_only_CC[0]
                            R_vol_spruce            = Results_Compound_Spruce1_only_CC[1]
                            trees_dict[t]           = Results_Compound_Spruce1_only_CC[2]
                            volsum[t]               = Results_Compound_Spruce1_only_CC[3]
                            vol_spruce[t]           = Results_Compound_Spruce1_only_CC[4]
                            vol_pine[t]             = Results_Compound_Spruce1_only_CC[5]
                            vol_birch[t]            = Results_Compound_Spruce1_only_CC[6]
                            vol_others[t]           = Results_Compound_Spruce1_only_CC[7]
                            vol_ROS[t]              = Results_Compound_Spruce1_only_CC[8]
                            vol_warm[t]             = Results_Compound_Spruce1_only_CC[9]
                            R_SPulp[t]              = Results_Compound_Spruce1_only_CC[10]
                            R_SSaw[t]               = Results_Compound_Spruce1_only_CC[11]
                            R_HSaw[t]               = Results_Compound_Spruce1_only_CC[12]
                            R_HPulp[t]              = Results_Compound_Spruce1_only_CC[13]
                            R_PSaw[t]               = Results_Compound_Spruce1_only_CC[14]
                            R_PPulp[t]              = Results_Compound_Spruce1_only_CC[15]
                            G_before                = Results_Compound_Spruce1_only_CC[16]
                            R_BA                    = Results_Compound_Spruce1_only_CC[17]
                            ba[t]                   = Results_Compound_Spruce1_only_CC[18]
                            BGB[t]                  = Results_Compound_Spruce1_only_CC[19]
                            Tot_co2[t]              = Results_Compound_Spruce1_only_CC[20]
                            Tot_biomass[t]          = Results_Compound_Spruce1_only_CC[21]
                            Total_carbon[t]         = Results_Compound_Spruce1_only_CC[22]
                            Tot_carbon_stems[t]     = Results_Compound_Spruce1_only_CC[23]
                            Tot_carbon_roots[t]     = Results_Compound_Spruce1_only_CC[24]
                            Tot_co2_stems[t]        = Results_Compound_Spruce1_only_CC[25]
                            Tot_co2_roots[t]        = Results_Compound_Spruce1_only_CC[26]

                                                                      
                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree
                            N_removed     = 0
                            R_vol_pine    = R_vol_pine
                            R_vol_birch   = R_vol_birch
                            R_vol_others  = R_vol_others
                            R_vol_ros     = R_vol_ros
                            R_vol_warm    = R_vol_warm
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0. 
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
            
            #mic_t == "High_pine"                                         
            elif CutFirst == "others_spruce":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):          
                        if (t in trees_others) and (len(trees_others_s7_toDelete) != 0):                                     
                            Results_1stCompound_others4_CC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_1stCompound_others4_CC[0]
                            R_vol_birch                 = Results_1stCompound_others4_CC[1]
                            R_vol_others                = Results_1stCompound_others4_CC[2]
                            R_vol_ros                   = Results_1stCompound_others4_CC[3]
                            R_vol_warm                  = Results_1stCompound_others4_CC[4]
                            trees_dict[t]               = Results_1stCompound_others4_CC[5]
                            volsum[t]                   = Results_1stCompound_others4_CC[6]
                            vol_spruce[t]               = Results_1stCompound_others4_CC[7]
                            vol_pine[t]                 = Results_1stCompound_others4_CC[8]
                            vol_birch[t]                = Results_1stCompound_others4_CC[9]
                            vol_others[t]               = Results_1stCompound_others4_CC[10]
                            vol_ROS[t]                  = Results_1stCompound_others4_CC[11]
                            vol_warm[t]                 = Results_1stCompound_others4_CC[12]
                            R_SPulp[t]                  = Results_1stCompound_others4_CC[13]
                            R_SSaw[t]                   = Results_1stCompound_others4_CC[14]
                            R_HSaw[t]                   = Results_1stCompound_others4_CC[15]
                            R_HPulp[t]                  = Results_1stCompound_others4_CC[16]
                            R_PSaw[t]                   = Results_1stCompound_others4_CC[17]
                            R_PPulp[t]                  = Results_1stCompound_others4_CC[18] 
                            G_before                    = Results_1stCompound_others4_CC[19]
                            R_BA                        = Results_1stCompound_others4_CC[20]
                            ba[t]                       = Results_1stCompound_others4_CC[21]
                            BGB[t]                      = Results_1stCompound_others4_CC[22]
                            Tot_co2[t]                  = Results_1stCompound_others4_CC[23]
                            Tot_biomass[t]              = Results_1stCompound_others4_CC[24]
                            Total_carbon[t]             = Results_1stCompound_others4_CC[25]
                            Tot_carbon_stems[t]         = Results_1stCompound_others4_CC[26]
                            Tot_carbon_roots[t]         = Results_1stCompound_others4_CC[27]
                            Tot_co2_stems[t]            = Results_1stCompound_others4_CC[28]
                            Tot_co2_roots[t]            = Results_1stCompound_others4_CC[29]
                            trees_others_s7_toDelete.remove(str(t))
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.  
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):                                           
                        if (t in trees_spruce) and len(trees_others_s7_toDelete) == 0:                 
                            Results_Compound_Spruce5_only_CC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed               = Results_Compound_Spruce5_only_CC[0]
                            R_vol_spruce            = Results_Compound_Spruce5_only_CC[1]
                            trees_dict[t]           = Results_Compound_Spruce5_only_CC[2]
                            volsum[t]               = Results_Compound_Spruce5_only_CC[3]
                            vol_spruce[t]           = Results_Compound_Spruce5_only_CC[4]
                            vol_pine[t]             = Results_Compound_Spruce5_only_CC[5]
                            vol_birch[t]            = Results_Compound_Spruce5_only_CC[6]
                            vol_others[t]           = Results_Compound_Spruce5_only_CC[7]
                            vol_ROS[t]              = Results_Compound_Spruce5_only_CC[8]
                            vol_warm[t]             = Results_Compound_Spruce5_only_CC[9]
                            R_SPulp[t]              = Results_Compound_Spruce5_only_CC[10]
                            R_SSaw[t]               = Results_Compound_Spruce5_only_CC[11]
                            R_HSaw[t]               = Results_Compound_Spruce5_only_CC[12]
                            R_HPulp[t]              = Results_Compound_Spruce5_only_CC[13]
                            R_PSaw[t]               = Results_Compound_Spruce5_only_CC[14]
                            R_PPulp[t]              = Results_Compound_Spruce5_only_CC[15]
                            G_before                = Results_Compound_Spruce5_only_CC[16]
                            R_BA                    = Results_Compound_Spruce5_only_CC[17]
                            ba[t]                   = Results_Compound_Spruce5_only_CC[18]
                            BGB[t]                  = Results_Compound_Spruce5_only_CC[19]
                            Tot_co2[t]              = Results_Compound_Spruce5_only_CC[20]
                            Tot_biomass[t]          = Results_Compound_Spruce5_only_CC[21]
                            Total_carbon[t]         = Results_Compound_Spruce5_only_CC[22]
                            Tot_carbon_stems[t]     = Results_Compound_Spruce5_only_CC[23]
                            Tot_carbon_roots[t]     = Results_Compound_Spruce5_only_CC[24]
                            Tot_co2_stems[t]        = Results_Compound_Spruce5_only_CC[25]
                            Tot_co2_roots[t]        = Results_Compound_Spruce5_only_CC[26]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.  

                        
             #mic_t == "High_pine" 
            elif (CutFirst ==  "spruce_others_pine"):
                for tree in trees:
                    t= tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and (len(trees_spruce_toDelete2) !=0):                               
                            Results_1stCompound_spruce2_CC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                       N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce2_CC[0]
                            R_vol_spruce               = Results_1stCompound_spruce2_CC[1]
                            trees_dict[t]              = Results_1stCompound_spruce2_CC[2]
                            volsum[t]                  = Results_1stCompound_spruce2_CC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce2_CC[4]
                            vol_pine[t]                = Results_1stCompound_spruce2_CC[5]
                            vol_birch[t]               = Results_1stCompound_spruce2_CC[6]
                            vol_others[t]              = Results_1stCompound_spruce2_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce2_CC[8]
                            vol_warm[t]                = Results_1stCompound_spruce2_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce2_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce2_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce2_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce2_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce2_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce2_CC[15]
                            G_before                   = Results_1stCompound_spruce2_CC[16]
                            R_BA                       = Results_1stCompound_spruce2_CC[17]
                            ba[t]                      = Results_1stCompound_spruce2_CC[18]
                            BGB[t]                     = Results_1stCompound_spruce2_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce2_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce2_CC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce2_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce2_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce2_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce2_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce2_CC[26]
                            trees_spruce_toDelete2.remove(str(t))
                                 
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                                                    
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):              
                        if (t in trees_others) and (len(trees_spruce_toDelete2) == 0) and (len(trees_others_s1_toDelete) != 0):  
                            Results_MCompound_others1_CC = self.MiddleCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                      Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,R_vol_others,
                                                                                      R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed               = Results_MCompound_others1_CC[0]
                            R_vol_birch             = Results_MCompound_others1_CC[1]
                            R_vol_others            = Results_MCompound_others1_CC[2]
                            R_vol_ros               = Results_MCompound_others1_CC[3]
                            R_vol_warm              = Results_MCompound_others1_CC[4]
                            trees_dict[t]           = Results_MCompound_others1_CC[5]
                            volsum[t]               = Results_MCompound_others1_CC[6]
                            vol_spruce[t]           = Results_MCompound_others1_CC[7]
                            vol_pine[t]             = Results_MCompound_others1_CC[8]
                            vol_birch[t]            = Results_MCompound_others1_CC[9]
                            vol_others[t]           = Results_MCompound_others1_CC[10]
                            vol_ROS[t]              = Results_MCompound_others1_CC[11]
                            vol_warm[t]             = Results_MCompound_others1_CC[12]
                            R_SPulp[t]              = Results_MCompound_others1_CC[13]
                            R_SSaw[t]               = Results_MCompound_others1_CC[14]
                            R_HSaw[t]               = Results_MCompound_others1_CC[15]
                            R_HPulp[t]              = Results_MCompound_others1_CC[16]
                            R_PSaw[t]               = Results_MCompound_others1_CC[17]
                            R_PPulp[t]              = Results_MCompound_others1_CC[18]
                            G_before                = Results_MCompound_others1_CC[19]
                            R_BA                    = Results_MCompound_others1_CC[20]
                            ba[t]                   = Results_MCompound_others1_CC[21]
                            BGB[t]                  = Results_MCompound_others1_CC[22]
                            Tot_co2[t]              = Results_MCompound_others1_CC[23]
                            Tot_biomass[t]          = Results_MCompound_others1_CC[24]
                            Total_carbon[t]         = Results_MCompound_others1_CC[25]
                            Tot_carbon_stems[t]     = Results_MCompound_others1_CC[26]
                            Tot_carbon_roots[t]     = Results_MCompound_others1_CC[27]
                            Tot_co2_stems[t]        = Results_MCompound_others1_CC[28]
                            Tot_co2_roots[t]        = Results_MCompound_others1_CC[29]
                            trees_others_s1_toDelete.remove(str(t))
                                
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and (len(trees_others_s1_toDelete) == 0) and (len(trees_spruce_toDelete2) == 0): 
                            Results_LastCompound_pine1_CC = self.LastCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine, 
                                                                                   N_removed, G_before)
                            N_removed               = Results_LastCompound_pine1_CC[0]
                            R_vol_pine              = Results_LastCompound_pine1_CC[1]
                            trees_dict[t]           = Results_LastCompound_pine1_CC[2]
                            volsum[t]               = Results_LastCompound_pine1_CC[3]
                            vol_spruce[t]           = Results_LastCompound_pine1_CC[4]
                            vol_pine[t]             = Results_LastCompound_pine1_CC[5]
                            vol_birch[t]            = Results_LastCompound_pine1_CC[6]
                            vol_others[t]           = Results_LastCompound_pine1_CC[7]
                            vol_ROS[t]              = Results_LastCompound_pine1_CC[8]
                            vol_warm[t]             = Results_LastCompound_pine1_CC[9]
                            R_SPulp[t]              = Results_LastCompound_pine1_CC[10]
                            R_SSaw[t]               = Results_LastCompound_pine1_CC[11]
                            R_HSaw[t]               = Results_LastCompound_pine1_CC[12]
                            R_HPulp[t]              = Results_LastCompound_pine1_CC[13]
                            R_PSaw[t]               = Results_LastCompound_pine1_CC[14]
                            R_PPulp[t]              = Results_LastCompound_pine1_CC[15]
                            G_before                = Results_LastCompound_pine1_CC[16]
                            R_BA                    = Results_LastCompound_pine1_CC[17]
                            ba[t]                   = Results_LastCompound_pine1_CC[18]
                            BGB[t]                  = Results_LastCompound_pine1_CC[19]
                            Tot_co2[t]              = Results_LastCompound_pine1_CC[20]
                            Tot_biomass[t]          = Results_LastCompound_pine1_CC[21]
                            Total_carbon[t]         = Results_LastCompound_pine1_CC[22]
                            Tot_carbon_stems[t]     = Results_LastCompound_pine1_CC[23]
                            Tot_carbon_roots[t]     = Results_LastCompound_pine1_CC[24]
                            Tot_co2_stems[t]        = Results_LastCompound_pine1_CC[25]
                            Tot_co2_roots[t]        = Results_LastCompound_pine1_CC[26]

                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.                                                         
             
            #mic_t == "High_pine"        
            elif CutFirst == "spruce_others":   
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and (len(trees_spruce_toDelete8) !=0): 
                            
                            Results_1stCompound_spruce7_CC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, 
                                                                                         Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                         N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce7_CC[0]
                            R_vol_spruce               = Results_1stCompound_spruce7_CC[1]
                            trees_dict[t]              = Results_1stCompound_spruce7_CC[2]
                            volsum[t]                  = Results_1stCompound_spruce7_CC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce7_CC[4]
                            vol_pine[t]                = Results_1stCompound_spruce7_CC[5]
                            vol_birch[t]               = Results_1stCompound_spruce7_CC[6]
                            vol_others[t]              = Results_1stCompound_spruce7_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce7_CC[8]
                            vol_warm[t]                = Results_1stCompound_spruce7_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce7_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce7_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce7_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce7_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce7_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce7_CC[15]  
                            G_before                   = Results_1stCompound_spruce7_CC[16]
                            R_BA                       = Results_1stCompound_spruce7_CC[17]
                            ba[t]                      = Results_1stCompound_spruce7_CC[18]
                            BGB[t]                     = Results_1stCompound_spruce7_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce7_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce7_CC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce7_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce7_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce7_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce7_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce7_CC[26]
                            trees_spruce_toDelete8.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                        
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and (len(trees_others_s6_toDelete) != 0) and (len(trees_spruce_toDelete8) == 0): 
                            
                            Results_2ndCompound_others5_CC = self.SecondCompound_Others(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, 
                                                                                        Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,R_vol_others,R_vol_ros,R_vol_warm ,
                                                                                        N_removed, G_before)                           
                            
                            N_removed                   = Results_2ndCompound_others5_CC[0]
                            R_vol_birch                 = Results_2ndCompound_others5_CC[1]
                            R_vol_others                = Results_2ndCompound_others5_CC[2]
                            R_vol_ros                   = Results_2ndCompound_others5_CC[3]
                            R_vol_warm                  = Results_2ndCompound_others5_CC[4]
                            trees_dict[t]               = Results_2ndCompound_others5_CC[5]
                            volsum[t]                   = Results_2ndCompound_others5_CC[6]
                            vol_spruce[t]               = Results_2ndCompound_others5_CC[7]
                            vol_pine[t]                 = Results_2ndCompound_others5_CC[8]
                            vol_birch[t]                = Results_2ndCompound_others5_CC[9]
                            vol_others[t]               = Results_2ndCompound_others5_CC[10]
                            vol_ROS[t]                  = Results_2ndCompound_others5_CC[11]
                            vol_warm[t]                 = Results_2ndCompound_others5_CC[12]
                            R_SPulp[t]                  = Results_2ndCompound_others5_CC[13]
                            R_SSaw[t]                   = Results_2ndCompound_others5_CC[14]
                            R_HSaw[t]                   = Results_2ndCompound_others5_CC[15]
                            R_HPulp[t]                  = Results_2ndCompound_others5_CC[16]
                            R_PSaw[t]                   = Results_2ndCompound_others5_CC[17]
                            R_PPulp[t]                  = Results_2ndCompound_others5_CC[18]
                            G_before                    = Results_2ndCompound_others5_CC[19]
                            R_BA                        = Results_2ndCompound_others5_CC[20]
                            ba[t]                       = Results_2ndCompound_others5_CC[21]
                            BGB[t]                      = Results_2ndCompound_others5_CC[22]
                            Tot_co2[t]                  = Results_2ndCompound_others5_CC[23]
                            Tot_biomass[t]              = Results_2ndCompound_others5_CC[24]
                            Total_carbon[t]             = Results_2ndCompound_others5_CC[25]
                            Tot_carbon_stems[t]         = Results_2ndCompound_others5_CC[26]
                            Tot_carbon_roots[t]         = Results_2ndCompound_others5_CC[27]
                            Tot_co2_stems[t]            = Results_2ndCompound_others5_CC[28]
                            Tot_co2_roots[t]            = Results_2ndCompound_others5_CC[29]
                            trees_others_s6_toDelete.remove(str(t))

                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                                                                            
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and (len(trees_spruce_toDelete8) == 0) and (len(trees_others_s6_toDelete) == 0):  

                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_pine    = R_vol_pine
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
            
            #mic_t == "High_pine"             
            elif (CutFirst == "pine_only"):
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_pine:
                            Results_1Compound_pine1_only_CC = self.Compound_pine_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                     N_removed, G_before)
                            N_removed               = Results_1Compound_pine1_only_CC[0]
                            R_vol_pine              = Results_1Compound_pine1_only_CC[1]
                            trees_dict[t]           = Results_1Compound_pine1_only_CC[2]
                            volsum[t]               = Results_1Compound_pine1_only_CC[3]
                            vol_spruce[t]           = Results_1Compound_pine1_only_CC[4]
                            vol_pine[t]             = Results_1Compound_pine1_only_CC[5]
                            vol_birch[t]            = Results_1Compound_pine1_only_CC[6]
                            vol_others[t]           = Results_1Compound_pine1_only_CC[7]
                            vol_ROS[t]              = Results_1Compound_pine1_only_CC[8]
                            vol_warm[t]             = Results_1Compound_pine1_only_CC[9]
                            R_SPulp[t]              = Results_1Compound_pine1_only_CC[10]
                            R_SSaw[t]               = Results_1Compound_pine1_only_CC[11]
                            R_HSaw[t]               = Results_1Compound_pine1_only_CC[12]
                            R_HPulp[t]              = Results_1Compound_pine1_only_CC[13]
                            R_PSaw[t]               = Results_1Compound_pine1_only_CC[14]
                            R_PPulp[t]              = Results_1Compound_pine1_only_CC[15]
                            G_before                = Results_1Compound_pine1_only_CC[16]
                            R_BA                    = Results_1Compound_pine1_only_CC[17]
                            ba[t]                   = Results_1Compound_pine1_only_CC[18]
                            BGB[t]                  = Results_1Compound_pine1_only_CC[19]
                            Tot_co2[t]              = Results_1Compound_pine1_only_CC[20]
                            Tot_biomass[t]          = Results_1Compound_pine1_only_CC[21]
                            Total_carbon[t]         = Results_1Compound_pine1_only_CC[22]
                            Tot_carbon_stems[t]     = Results_1Compound_pine1_only_CC[23]
                            Tot_carbon_roots[t]     = Results_1Compound_pine1_only_CC[24]
                            Tot_co2_stems[t]        = Results_1Compound_pine1_only_CC[25]
                            Tot_co2_roots[t]        = Results_1Compound_pine1_only_CC[26]
                                                                      
                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree
                            N_removed     = 0
                            R_vol_spruce  = R_vol_spruce
                            R_vol_birch   = R_vol_birch
                            R_vol_others  = R_vol_others
                            R_vol_ros     = R_vol_ros
                            R_vol_warm    = R_vol_warm
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0. 
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
             
        elif mic_t in [ "High_spruce", "Medium_spruce",  "Low_spruce"]:
            if (CutFirst ==  "pine_spruce"):
                for tree in trees:
                    t = tree 
                    if (G_before > BA_left):                                          
                        if (t in trees_pine) and (len(trees_pine_toDelete1) != 0):                                                      
                            Results_1stCompound_pine1_CC = self.firstCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine,
                                                                                   N_removed, G_before)
                            N_removed                  = Results_1stCompound_pine1_CC[0]
                            R_vol_pine                 = Results_1stCompound_pine1_CC[1]
                            trees_dict[t]              = Results_1stCompound_pine1_CC[2]
                            volsum[t]                  = Results_1stCompound_pine1_CC[3]
                            vol_spruce[t]              = Results_1stCompound_pine1_CC[4]
                            vol_pine[t]                = Results_1stCompound_pine1_CC[5]
                            vol_birch[t]               = Results_1stCompound_pine1_CC[6]
                            vol_others[t]              = Results_1stCompound_pine1_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_pine1_CC[8]
                            vol_warm[t]                = Results_1stCompound_pine1_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_pine1_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_pine1_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_pine1_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_pine1_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_pine1_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_pine1_CC[15]
                            G_before                   = Results_1stCompound_pine1_CC[16]
                            R_BA                       = Results_1stCompound_pine1_CC[17]
                            ba[t]                      = Results_1stCompound_pine1_CC[18]
                            BGB[t]                     = Results_1stCompound_pine1_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_pine1_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_pine1_CC[21]
                            Total_carbon[t]            = Results_1stCompound_pine1_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_pine1_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_pine1_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_pine1_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_pine1_CC[26]
                            trees_pine_toDelete1.remove(str(t))
                                                  
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_spruce)  and len(trees_pine_toDelete1) == 0: 
                            Results_2ndCompound_Spruce1_CC = self.Compound_Spruce_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                       N_removed, G_before)
                            N_removed               = Results_2ndCompound_Spruce1_CC[0]
                            R_vol_spruce            = Results_2ndCompound_Spruce1_CC[1]
                            trees_dict[t]           = Results_2ndCompound_Spruce1_CC[2]
                            volsum[t]               = Results_2ndCompound_Spruce1_CC[3]
                            vol_spruce[t]           = Results_2ndCompound_Spruce1_CC[4]
                            vol_pine[t]             = Results_2ndCompound_Spruce1_CC[5]
                            vol_birch[t]            = Results_2ndCompound_Spruce1_CC[6]
                            vol_others[t]           = Results_2ndCompound_Spruce1_CC[7]
                            vol_ROS[t]              = Results_2ndCompound_Spruce1_CC[8]
                            vol_warm[t]             = Results_2ndCompound_Spruce1_CC[9]
                            R_SPulp[t]              = Results_2ndCompound_Spruce1_CC[10]
                            R_SSaw[t]               = Results_2ndCompound_Spruce1_CC[11]
                            R_HSaw[t]               = Results_2ndCompound_Spruce1_CC[12]
                            R_HPulp[t]              = Results_2ndCompound_Spruce1_CC[13]
                            R_PSaw[t]               = Results_2ndCompound_Spruce1_CC[14]
                            R_PPulp[t]              = Results_2ndCompound_Spruce1_CC[15]
                            G_before                = Results_2ndCompound_Spruce1_CC[16]
                            R_BA                    = Results_2ndCompound_Spruce1_CC[17]
                            ba[t]                   = Results_2ndCompound_Spruce1_CC[18]
                            BGB[t]                  = Results_2ndCompound_Spruce1_CC[19]
                            Tot_co2[t]              = Results_2ndCompound_Spruce1_CC[20]
                            Tot_biomass[t]          = Results_2ndCompound_Spruce1_CC[21]
                            Total_carbon[t]         = Results_2ndCompound_Spruce1_CC[22]
                            Tot_carbon_stems[t]     = Results_2ndCompound_Spruce1_CC[23]
                            Tot_carbon_roots[t]     = Results_2ndCompound_Spruce1_CC[24]
                            Tot_co2_stems[t]        = Results_2ndCompound_Spruce1_CC[25]
                            Tot_co2_roots[t]        = Results_2ndCompound_Spruce1_CC[26]
                        
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                
                for tree in trees:
                    t = tree
                    if (t in trees_others)  and (len(trees_pine_toDelete1) == 0): 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree 
                        N_removed     = 0
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 

            #[ "High_spruce", "Medium_spruce",  "Low_spruce"]                                                                 
            elif (CutFirst == "pine_only"):
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_pine:
                            Results_1Compound_pine_only_CC = self.Compound_pine_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                     N_removed, G_before)
                            N_removed               = Results_1Compound_pine_only_CC[0]
                            R_vol_pine              = Results_1Compound_pine_only_CC[1]
                            trees_dict[t]           = Results_1Compound_pine_only_CC[2]
                            volsum[t]               = Results_1Compound_pine_only_CC[3]
                            vol_spruce[t]           = Results_1Compound_pine_only_CC[4]
                            vol_pine[t]             = Results_1Compound_pine_only_CC[5]
                            vol_birch[t]            = Results_1Compound_pine_only_CC[6]
                            vol_others[t]           = Results_1Compound_pine_only_CC[7]
                            vol_ROS[t]              = Results_1Compound_pine_only_CC[8]
                            vol_warm[t]             = Results_1Compound_pine_only_CC[9]
                            R_SPulp[t]              = Results_1Compound_pine_only_CC[10]
                            R_SSaw[t]               = Results_1Compound_pine_only_CC[11]
                            R_HSaw[t]               = Results_1Compound_pine_only_CC[12]
                            R_HPulp[t]              = Results_1Compound_pine_only_CC[13]
                            R_PSaw[t]               = Results_1Compound_pine_only_CC[14]
                            R_PPulp[t]              = Results_1Compound_pine_only_CC[15]
                            G_before                = Results_1Compound_pine_only_CC[16]
                            R_BA                    = Results_1Compound_pine_only_CC[17]
                            ba[t]                   = Results_1Compound_pine_only_CC[18]
                            BGB[t]                  = Results_1Compound_pine_only_CC[19]
                            Tot_co2[t]              = Results_1Compound_pine_only_CC[20]
                            Tot_biomass[t]          = Results_1Compound_pine_only_CC[21]
                            Total_carbon[t]         = Results_1Compound_pine_only_CC[22]
                            Tot_carbon_stems[t]     = Results_1Compound_pine_only_CC[23]
                            Tot_carbon_roots[t]     = Results_1Compound_pine_only_CC[24]
                            Tot_co2_stems[t]        = Results_1Compound_pine_only_CC[25]
                            Tot_co2_roots[t]        = Results_1Compound_pine_only_CC[26]
                                                                      
                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree
                            N_removed     = 0
                            R_vol_spruce  = R_vol_spruce
                            R_vol_birch   = R_vol_birch
                            R_vol_others  = R_vol_others
                            R_vol_ros     = R_vol_ros
                            R_vol_warm    = R_vol_warm
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0. 
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 

            #[ "High_spruce", "Medium_spruce",  "Low_spruce"]            
            elif (CutFirst ==  "spruce_only"):
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_spruce:
                            Results_Compound_Spruce2_only_CC = self.Compound_Spruce_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed               = Results_Compound_Spruce2_only_CC[0]
                            R_vol_spruce            = Results_Compound_Spruce2_only_CC[1]
                            trees_dict[t]           = Results_Compound_Spruce2_only_CC[2]
                            volsum[t]               = Results_Compound_Spruce2_only_CC[3]
                            vol_spruce[t]           = Results_Compound_Spruce2_only_CC[4]
                            vol_pine[t]             = Results_Compound_Spruce2_only_CC[5]
                            vol_birch[t]            = Results_Compound_Spruce2_only_CC[6]
                            vol_others[t]           = Results_Compound_Spruce2_only_CC[7]
                            vol_ROS[t]              = Results_Compound_Spruce2_only_CC[8]
                            vol_warm[t]             = Results_Compound_Spruce2_only_CC[9]
                            R_SPulp[t]              = Results_Compound_Spruce2_only_CC[10]
                            R_SSaw[t]               = Results_Compound_Spruce2_only_CC[11]
                            R_HSaw[t]               = Results_Compound_Spruce2_only_CC[12]
                            R_HPulp[t]              = Results_Compound_Spruce2_only_CC[13]
                            R_PSaw[t]               = Results_Compound_Spruce2_only_CC[14]
                            R_PPulp[t]              = Results_Compound_Spruce2_only_CC[15]
                            G_before                = Results_Compound_Spruce2_only_CC[16]
                            R_BA                    = Results_Compound_Spruce2_only_CC[17]
                            ba[t]                   = Results_Compound_Spruce2_only_CC[18]
                            BGB[t]                  = Results_Compound_Spruce2_only_CC[19]
                            Tot_co2[t]              = Results_Compound_Spruce2_only_CC[20]
                            Tot_biomass[t]          = Results_Compound_Spruce2_only_CC[21]
                            Total_carbon[t]         = Results_Compound_Spruce2_only_CC[22]
                            Tot_carbon_stems[t]     = Results_Compound_Spruce2_only_CC[23]
                            Tot_carbon_roots[t]     = Results_Compound_Spruce2_only_CC[24]
                            Tot_co2_stems[t]        = Results_Compound_Spruce2_only_CC[25]
                            Tot_co2_roots[t]        = Results_Compound_Spruce2_only_CC[26]
                            
                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree
                            N_removed     = 0
                            R_vol_pine    = R_vol_pine
                            R_vol_birch   = R_vol_birch
                            R_vol_others  = R_vol_others
                            R_vol_ros     = R_vol_ros
                            R_vol_warm    = R_vol_warm
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0. 
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                                 
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree 
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                                                 
            #[ "High_spruce", "Medium_spruce",  "Low_spruce"]  

            elif CutFirst == "others_pine":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):                        
                        if (t in trees_others) and (len(trees_others_p4_toDelete) != 0):    
                            Results_1stCompound_others6_CC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed               = Results_1stCompound_others6_CC[0]
                            R_vol_birch             = Results_1stCompound_others6_CC[1]
                            R_vol_others            = Results_1stCompound_others6_CC[2]
                            R_vol_ros               = Results_1stCompound_others6_CC[3]
                            R_vol_warm              = Results_1stCompound_others6_CC[4]
                            trees_dict[t]           = Results_1stCompound_others6_CC[5]
                            volsum[t]               = Results_1stCompound_others6_CC[6]
                            vol_spruce[t]           = Results_1stCompound_others6_CC[7]
                            vol_pine[t]             = Results_1stCompound_others6_CC[8]
                            vol_birch[t]            = Results_1stCompound_others6_CC[9]
                            vol_others[t]           = Results_1stCompound_others6_CC[10]
                            vol_ROS[t]              = Results_1stCompound_others6_CC[11]
                            vol_warm[t]             = Results_1stCompound_others6_CC[12]
                            R_SPulp[t]              = Results_1stCompound_others6_CC[13]
                            R_SSaw[t]               = Results_1stCompound_others6_CC[14]
                            R_HSaw[t]               = Results_1stCompound_others6_CC[15]
                            R_HPulp[t]              = Results_1stCompound_others6_CC[16]
                            R_PSaw[t]               = Results_1stCompound_others6_CC[17]
                            R_PPulp[t]              = Results_1stCompound_others6_CC[18]
                            G_before                = Results_1stCompound_others6_CC[19]
                            R_BA                    = Results_1stCompound_others6_CC[20]
                            ba[t]                   = Results_1stCompound_others6_CC[21]
                            BGB[t]                  = Results_1stCompound_others6_CC[22]
                            Tot_co2[t]              = Results_1stCompound_others6_CC[23]
                            Tot_biomass[t]          = Results_1stCompound_others6_CC[24]
                            Total_carbon[t]         = Results_1stCompound_others6_CC[25]
                            Tot_carbon_stems[t]     = Results_1stCompound_others6_CC[26]
                            Tot_carbon_roots[t]     = Results_1stCompound_others6_CC[27]
                            Tot_co2_stems[t]        = Results_1stCompound_others6_CC[28]
                            Tot_co2_roots[t]        = Results_1stCompound_others6_CC[29]
                            trees_others_p4_toDelete.remove(str(t))
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                                
                for tree in trees:
                    t = tree   
                    if (G_before > BA_left):
                        if (t in trees_pine) and len(trees_others_p4_toDelete) == 0:
                            Results_2ndCompound_pine7_CC = self.Compound_pine_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                   N_removed, G_before)
                            N_removed               = Results_2ndCompound_pine7_CC[0]
                            R_vol_pine            = Results_2ndCompound_pine7_CC[1]
                            trees_dict[t]           = Results_2ndCompound_pine7_CC[2]
                            volsum[t]               = Results_2ndCompound_pine7_CC[3]
                            vol_spruce[t]           = Results_2ndCompound_pine7_CC[4]
                            vol_pine[t]             = Results_2ndCompound_pine7_CC[5]
                            vol_birch[t]            = Results_2ndCompound_pine7_CC[6]
                            vol_others[t]           = Results_2ndCompound_pine7_CC[7]
                            vol_ROS[t]              = Results_2ndCompound_pine7_CC[8]
                            vol_warm[t]             = Results_2ndCompound_pine7_CC[9]
                            R_SPulp[t]              = Results_2ndCompound_pine7_CC[10]
                            R_SSaw[t]               = Results_2ndCompound_pine7_CC[11]
                            R_HSaw[t]               = Results_2ndCompound_pine7_CC[12]
                            R_HPulp[t]              = Results_2ndCompound_pine7_CC[13]
                            R_PSaw[t]               = Results_2ndCompound_pine7_CC[14]
                            R_PPulp[t]              = Results_2ndCompound_pine7_CC[15]
                            G_before                = Results_2ndCompound_pine7_CC[16]
                            R_BA                    = Results_2ndCompound_pine7_CC[17]
                            ba[t]                   = Results_2ndCompound_pine7_CC[18]
                            BGB[t]                  = Results_2ndCompound_pine7_CC[19]
                            Tot_co2[t]              = Results_2ndCompound_pine7_CC[20]
                            Tot_biomass[t]          = Results_2ndCompound_pine7_CC[21]
                            Total_carbon[t]         = Results_2ndCompound_pine7_CC[22]
                            Tot_carbon_stems[t]     = Results_2ndCompound_pine7_CC[23]
                            Tot_carbon_roots[t]     = Results_2ndCompound_pine7_CC[24]
                            Tot_co2_stems[t]        = Results_2ndCompound_pine7_CC[25]
                            Tot_co2_roots[t]        = Results_2ndCompound_pine7_CC[26]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                            
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and len(trees_others_p4_toDelete) == 0: 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree 
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 
                        
            #[ "High_spruce", "Medium_spruce",  "Low_spruce"] 
            elif (CutFirst == "spruce_pine"): 
                for tree in trees:
                    t= tree
                    if (G_before > BA_left):                                        
                        if (t in trees_spruce) and (len(trees_spruce_toDelete3) != 0): 
                            Results_1stCompound_spruce3_CC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                       N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce3_CC[0]
                            R_vol_spruce               = Results_1stCompound_spruce3_CC[1]
                            trees_dict[t]              = Results_1stCompound_spruce3_CC[2]
                            volsum[t]                  = Results_1stCompound_spruce3_CC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce3_CC[4]
                            vol_pine[t]                = Results_1stCompound_spruce3_CC[5]
                            vol_birch[t]               = Results_1stCompound_spruce3_CC[6]
                            vol_others[t]              = Results_1stCompound_spruce3_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce3_CC[8]
                            vol_warm[t]                = Results_1stCompound_spruce3_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce3_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce3_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce3_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce3_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce3_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce3_CC[15]
                            G_before                   = Results_1stCompound_spruce3_CC[16]
                            R_BA                       = Results_1stCompound_spruce3_CC[17]
                            ba[t]                      = Results_1stCompound_spruce3_CC[18]
                            BGB[t]                     = Results_1stCompound_spruce3_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce3_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce3_CC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce3_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce3_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce3_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce3_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce3_CC[26]
                            trees_spruce_toDelete3.remove(str(t)) 
                                
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum        = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce    = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine      = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch     = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others    = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS       = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm      = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                           
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and len(trees_spruce_toDelete3) == 0:
                            Results_2ndCompound_pine2_CC = self.LastCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                  Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine, 
                                                                                  N_removed, G_before)
                            N_removed               = Results_2ndCompound_pine2_CC[0]
                            R_vol_pine              = Results_2ndCompound_pine2_CC[1]
                            trees_dict[t]           = Results_2ndCompound_pine2_CC[2]
                            volsum[t]               = Results_2ndCompound_pine2_CC[3]
                            vol_spruce[t]           = Results_2ndCompound_pine2_CC[4]
                            vol_pine[t]             = Results_2ndCompound_pine2_CC[5]
                            vol_birch[t]            = Results_2ndCompound_pine2_CC[6]
                            vol_others[t]           = Results_2ndCompound_pine2_CC[7]
                            vol_ROS[t]              = Results_2ndCompound_pine2_CC[8]
                            vol_warm[t]             = Results_2ndCompound_pine2_CC[9]
                            R_SPulp[t]              = Results_2ndCompound_pine2_CC[10]
                            R_SSaw[t]               = Results_2ndCompound_pine2_CC[11]
                            R_HSaw[t]               = Results_2ndCompound_pine2_CC[12]
                            R_HPulp[t]              = Results_2ndCompound_pine2_CC[13]
                            R_PSaw[t]               = Results_2ndCompound_pine2_CC[14]
                            R_PPulp[t]              = Results_2ndCompound_pine2_CC[15]
                            G_before                = Results_2ndCompound_pine2_CC[16]
                            R_BA                    = Results_2ndCompound_pine2_CC[17]
                            ba[t]                   = Results_2ndCompound_pine2_CC[18]
                            BGB[t]                  = Results_2ndCompound_pine2_CC[19]
                            Tot_co2[t]              = Results_2ndCompound_pine2_CC[20]
                            Tot_biomass[t]          = Results_2ndCompound_pine2_CC[21]
                            Total_carbon[t]         = Results_2ndCompound_pine2_CC[22]
                            Tot_carbon_stems[t]     = Results_2ndCompound_pine2_CC[23]
                            Tot_carbon_roots[t]     = Results_2ndCompound_pine2_CC[24]
                            Tot_co2_stems[t]        = Results_2ndCompound_pine2_CC[25]
                            Tot_co2_roots[t]        = Results_2ndCompound_pine2_CC[26]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                      
                for tree in trees: 
                    t = tree
                    if (t in trees_others) and len(trees_spruce_toDelete3) == 0: 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]   = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]  = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw[t]    = 0.
                        R_HPulp[t]   = 0.
                        R_SSaw[t]    = 0.
                        R_SPulp[t]   = 0.
                        R_PSaw[t]    = 0.
                        R_PPulp[t]   = 0.                       
                        
            ##[ "High_spruce", "Medium_spruce",  "Low_spruce"]
            elif CutFirst == "spruce_pine_others":
                for tree in trees:
                    t= tree
                    if (G_before > BA_left):                    
                        if (t in trees_spruce) and (len(trees_spruce_toDelete4) !=0): 
                            Results_1stCompound_spruce4_CC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                       N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce4_CC[0]
                            R_vol_spruce               = Results_1stCompound_spruce4_CC[1]
                            trees_dict[t]              = Results_1stCompound_spruce4_CC[2]
                            volsum[t]                  = Results_1stCompound_spruce4_CC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce4_CC[4]
                            vol_pine[t]                = Results_1stCompound_spruce4_CC[5]
                            vol_birch[t]               = Results_1stCompound_spruce4_CC[6]
                            vol_others[t]              = Results_1stCompound_spruce4_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce4_CC[8]
                            vol_warm[t]                = Results_1stCompound_spruce4_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce4_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce4_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce4_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce4_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce4_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce4_CC[15] 
                            G_before                   = Results_1stCompound_spruce4_CC[16]
                            R_BA                       = Results_1stCompound_spruce4_CC[17]
                            ba[t]                      = Results_1stCompound_spruce4_CC[18]
                            BGB[t]                     = Results_1stCompound_spruce4_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce4_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce4_CC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce4_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce4_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce4_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce4_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce4_CC[26]
                            trees_spruce_toDelete4.remove(str(t))
                                 
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree 
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                                                  
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and (len(trees_spruce_toDelete4) == 0) and (len(trees_pine_toDelete2) != 0):                                            
                            Results_2ndCompound_pine3_CC = self.firstCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine,
                                                                                   N_removed, G_before)
                            N_removed                  = Results_2ndCompound_pine3_CC[0]
                            R_vol_pine                 = Results_2ndCompound_pine3_CC[1]
                            trees_dict[t]              = Results_2ndCompound_pine3_CC[2]
                            volsum[t]                  = Results_2ndCompound_pine3_CC[3]
                            vol_spruce[t]              = Results_2ndCompound_pine3_CC[4]
                            vol_pine[t]                = Results_2ndCompound_pine3_CC[5]
                            vol_birch[t]               = Results_2ndCompound_pine3_CC[6]
                            vol_others[t]              = Results_2ndCompound_pine3_CC[7]
                            vol_ROS[t]                 = Results_2ndCompound_pine3_CC[8]
                            vol_warm[t]                = Results_2ndCompound_pine3_CC[9]
                            R_SPulp[t]                 = Results_2ndCompound_pine3_CC[10]
                            R_SSaw[t]                  = Results_2ndCompound_pine3_CC[11]
                            R_HSaw[t]                  = Results_2ndCompound_pine3_CC[12]
                            R_HPulp[t]                 = Results_2ndCompound_pine3_CC[13]
                            R_PSaw[t]                  = Results_2ndCompound_pine3_CC[14]
                            R_PPulp[t]                 = Results_2ndCompound_pine3_CC[15]
                            G_before                   = Results_2ndCompound_pine3_CC[16]
                            R_BA                       = Results_2ndCompound_pine3_CC[17]
                            ba[t]                      = Results_2ndCompound_pine3_CC[18]
                            BGB[t]                     = Results_2ndCompound_pine3_CC[19]
                            Tot_co2[t]                 = Results_2ndCompound_pine3_CC[20]
                            Tot_biomass[t]             = Results_2ndCompound_pine3_CC[21]
                            Total_carbon[t]            = Results_2ndCompound_pine3_CC[22]
                            Tot_carbon_stems[t]        = Results_2ndCompound_pine3_CC[23]
                            Tot_carbon_roots[t]        = Results_2ndCompound_pine3_CC[24]
                            Tot_co2_stems[t]           = Results_2ndCompound_pine3_CC[25]
                            Tot_co2_roots[t]           = Results_2ndCompound_pine3_CC[26]
                            trees_pine_toDelete2.remove(str(t))
                              
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 

                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and (len(trees_pine_toDelete2) == 0) and (len(trees_spruce_toDelete4) == 0):   
                            Results_LastCompound_others1_CC = self.SecondCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                         R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_LastCompound_others1_CC[0]
                            R_vol_birch                 = Results_LastCompound_others1_CC[1]
                            R_vol_others                = Results_LastCompound_others1_CC[2]
                            R_vol_ros                   = Results_LastCompound_others1_CC[3]
                            R_vol_warm                  = Results_LastCompound_others1_CC[4]
                            trees_dict[t]               = Results_LastCompound_others1_CC[5]
                            volsum[t]                   = Results_LastCompound_others1_CC[6]
                            vol_spruce[t]               = Results_LastCompound_others1_CC[7]
                            vol_pine[t]                 = Results_LastCompound_others1_CC[8]
                            vol_birch[t]                = Results_LastCompound_others1_CC[9]
                            vol_others[t]               = Results_LastCompound_others1_CC[10]
                            vol_ROS[t]                  = Results_LastCompound_others1_CC[11]
                            vol_warm[t]                 = Results_LastCompound_others1_CC[12]
                            R_SPulp[t]                  = Results_LastCompound_others1_CC[13]
                            R_SSaw[t]                   = Results_LastCompound_others1_CC[14]
                            R_HSaw[t]                   = Results_LastCompound_others1_CC[15]
                            R_HPulp[t]                  = Results_LastCompound_others1_CC[16]
                            R_PSaw[t]                   = Results_LastCompound_others1_CC[17]
                            R_PPulp[t]                  = Results_LastCompound_others1_CC[18]
                            G_before                    = Results_LastCompound_others1_CC[19]
                            R_BA                        = Results_LastCompound_others1_CC[20]
                            ba[t]                       = Results_LastCompound_others1_CC[21]
                            BGB[t]                      = Results_LastCompound_others1_CC[22]
                            Tot_co2[t]                  = Results_LastCompound_others1_CC[23]
                            Tot_biomass[t]              = Results_LastCompound_others1_CC[24]
                            Total_carbon[t]             = Results_LastCompound_others1_CC[25]
                            Tot_carbon_stems[t]         = Results_LastCompound_others1_CC[26]
                            Tot_carbon_roots[t]         = Results_LastCompound_others1_CC[27]
                            Tot_co2_stems[t]            = Results_LastCompound_others1_CC[28]
                            Tot_co2_roots[t]            = Results_LastCompound_others1_CC[29]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 

            ##[ "High_spruce", "Medium_spruce",  "Low_spruce"]
            elif CutFirst == "spruce_others_pine":
                for tree in trees:
                    t= tree
                    if (G_before > BA_left):                    
                        if (t in trees_spruce) and (len(trees_spruce_toDelete7) !=0): 
                            Results_1stCompound_spruce6_CC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                       N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce6_CC[0]
                            R_vol_spruce               = Results_1stCompound_spruce6_CC[1]
                            trees_dict[t]              = Results_1stCompound_spruce6_CC[2]
                            volsum[t]                  = Results_1stCompound_spruce6_CC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce6_CC[4]
                            vol_pine[t]                = Results_1stCompound_spruce6_CC[5]
                            vol_birch[t]               = Results_1stCompound_spruce6_CC[6]
                            vol_others[t]              = Results_1stCompound_spruce6_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce6_CC[8]
                            vol_warm[t]                = Results_1stCompound_spruce6_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce6_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce6_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce6_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce6_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce6_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce6_CC[15] 
                            G_before                   = Results_1stCompound_spruce6_CC[16]
                            R_BA                       = Results_1stCompound_spruce6_CC[17]
                            ba[t]                      = Results_1stCompound_spruce6_CC[18]
                            BGB[t]                     = Results_1stCompound_spruce6_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce6_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce6_CC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce6_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce6_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce6_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce6_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce6_CC[26]
                            trees_spruce_toDelete7.remove(str(t))
                                 
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree 
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                                                  
                for tree in trees: 
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and (len(trees_spruce_toDelete7) == 0) and (len(trees_others_p3_toDelete) != 0):                                            
                            Results_LastCompound_others2_CC = self.SecondCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                         R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_LastCompound_others2_CC[0]
                            R_vol_birch                 = Results_LastCompound_others2_CC[1]
                            R_vol_others                = Results_LastCompound_others2_CC[2]
                            R_vol_ros                   = Results_LastCompound_others2_CC[3]
                            R_vol_warm                  = Results_LastCompound_others2_CC[4]
                            trees_dict[t]               = Results_LastCompound_others2_CC[5]
                            volsum[t]                   = Results_LastCompound_others2_CC[6]
                            vol_spruce[t]               = Results_LastCompound_others2_CC[7]
                            vol_pine[t]                 = Results_LastCompound_others2_CC[8]
                            vol_birch[t]                = Results_LastCompound_others2_CC[9]
                            vol_others[t]               = Results_LastCompound_others2_CC[10]
                            vol_ROS[t]                  = Results_LastCompound_others2_CC[11]
                            vol_warm[t]                 = Results_LastCompound_others2_CC[12]
                            R_SPulp[t]                  = Results_LastCompound_others2_CC[13]
                            R_SSaw[t]                   = Results_LastCompound_others2_CC[14]
                            R_HSaw[t]                   = Results_LastCompound_others2_CC[15]
                            R_HPulp[t]                  = Results_LastCompound_others2_CC[16]
                            R_PSaw[t]                   = Results_LastCompound_others2_CC[17]
                            R_PPulp[t]                  = Results_LastCompound_others2_CC[18]
                            G_before                    = Results_LastCompound_others2_CC[19]
                            R_BA                        = Results_LastCompound_others2_CC[20]
                            ba[t]                       = Results_LastCompound_others2_CC[21]
                            BGB[t]                      = Results_LastCompound_others2_CC[22]
                            Tot_co2[t]                  = Results_LastCompound_others2_CC[23]
                            Tot_biomass[t]              = Results_LastCompound_others2_CC[24]
                            Total_carbon[t]             = Results_LastCompound_others2_CC[25]
                            Tot_carbon_stems[t]         = Results_LastCompound_others2_CC[26]
                            Tot_carbon_roots[t]         = Results_LastCompound_others2_CC[27]
                            Tot_co2_stems[t]            = Results_LastCompound_others2_CC[28]
                            Tot_co2_roots[t]            = Results_LastCompound_others2_CC[29]
                            trees_others_p3_toDelete.remove(str(t))
                        
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 

                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and (len(trees_others_p3_toDelete) == 0) and (len(trees_spruce_toDelete7) == 0):
                            Results_2ndCompound_pine6_CC = self.firstCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine,
                                                                                   N_removed, G_before)
                            N_removed                  = Results_2ndCompound_pine6_CC[0]
                            R_vol_pine                 = Results_2ndCompound_pine6_CC[1]
                            trees_dict[t]              = Results_2ndCompound_pine6_CC[2]
                            volsum[t]                  = Results_2ndCompound_pine6_CC[3]
                            vol_spruce[t]              = Results_2ndCompound_pine6_CC[4]
                            vol_pine[t]                = Results_2ndCompound_pine6_CC[5]
                            vol_birch[t]               = Results_2ndCompound_pine6_CC[6]
                            vol_others[t]              = Results_2ndCompound_pine6_CC[7]
                            vol_ROS[t]                 = Results_2ndCompound_pine6_CC[8]
                            vol_warm[t]                = Results_2ndCompound_pine6_CC[9]
                            R_SPulp[t]                 = Results_2ndCompound_pine6_CC[10]
                            R_SSaw[t]                  = Results_2ndCompound_pine6_CC[11]
                            R_HSaw[t]                  = Results_2ndCompound_pine6_CC[12]
                            R_HPulp[t]                 = Results_2ndCompound_pine6_CC[13]
                            R_PSaw[t]                  = Results_2ndCompound_pine6_CC[14]
                            R_PPulp[t]                 = Results_2ndCompound_pine6_CC[15]
                            G_before                   = Results_2ndCompound_pine6_CC[16]
                            R_BA                       = Results_2ndCompound_pine6_CC[17]
                            ba[t]                      = Results_2ndCompound_pine6_CC[18]
                            BGB[t]                     = Results_2ndCompound_pine6_CC[19]
                            Tot_co2[t]                 = Results_2ndCompound_pine6_CC[20]
                            Tot_biomass[t]             = Results_2ndCompound_pine6_CC[21]
                            Total_carbon[t]            = Results_2ndCompound_pine6_CC[22]
                            Tot_carbon_stems[t]        = Results_2ndCompound_pine6_CC[23]
                            Tot_carbon_roots[t]        = Results_2ndCompound_pine6_CC[24]
                            Tot_co2_stems[t]           = Results_2ndCompound_pine6_CC[25]
                            Tot_co2_roots[t]           = Results_2ndCompound_pine6_CC[26]

                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.             
            
            ##[ "High_spruce", "Medium_spruce",  "Low_spruce"] 
            elif CutFirst == "pine_others":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and len(trees_pine_toDelete4)!= 0:                                     
                            Results_1stCompound_pine3_CC = self.firstCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine,
                                                                                   N_removed, G_before)
                            N_removed                  = Results_1stCompound_pine3_CC[0]
                            R_vol_pine                 = Results_1stCompound_pine3_CC[1]
                            trees_dict[t]              = Results_1stCompound_pine3_CC[2]
                            volsum[t]                  = Results_1stCompound_pine3_CC[3]
                            vol_spruce[t]              = Results_1stCompound_pine3_CC[4]
                            vol_pine[t]                = Results_1stCompound_pine3_CC[5]
                            vol_birch[t]               = Results_1stCompound_pine3_CC[6]
                            vol_others[t]              = Results_1stCompound_pine3_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_pine3_CC[8]
                            vol_warm[t]                = Results_1stCompound_pine3_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_pine3_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_pine3_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_pine3_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_pine3_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_pine3_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_pine3_CC[15]
                            G_before                   = Results_1stCompound_pine3_CC[16]
                            R_BA                       = Results_1stCompound_pine3_CC[17]
                            ba[t]                      = Results_1stCompound_pine3_CC[18]
                            BGB[t]                     = Results_1stCompound_pine3_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_pine3_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_pine3_CC[21]
                            Total_carbon[t]            = Results_1stCompound_pine3_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_pine3_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_pine3_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_pine3_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_pine3_CC[26]
                            trees_pine_toDelete4.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm      = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.  
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):       
                        if (t in trees_others) and len(trees_pine_toDelete4) == 0:                 
                            Results_2ndCompound_others6_CC = self.SecondCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                        Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,R_vol_others,
                                                                                        R_vol_ros,R_vol_warm ,N_removed, G_before)                        
                            N_removed                   = Results_2ndCompound_others6_CC[0]
                            R_vol_birch                 = Results_2ndCompound_others6_CC[1]
                            R_vol_others                = Results_2ndCompound_others6_CC[2]
                            R_vol_ros                   = Results_2ndCompound_others6_CC[3]
                            R_vol_warm                  = Results_2ndCompound_others6_CC[4]
                            trees_dict[t]               = Results_2ndCompound_others6_CC[5]
                            volsum[t]                   = Results_2ndCompound_others6_CC[6]
                            vol_spruce[t]               = Results_2ndCompound_others6_CC[7]
                            vol_pine[t]                 = Results_2ndCompound_others6_CC[8]
                            vol_birch[t]                = Results_2ndCompound_others6_CC[9]
                            vol_others[t]               = Results_2ndCompound_others6_CC[10]
                            vol_ROS[t]                  = Results_2ndCompound_others6_CC[11]
                            vol_warm[t]                 = Results_2ndCompound_others6_CC[12]
                            R_SPulp[t]                  = Results_2ndCompound_others6_CC[13]
                            R_SSaw[t]                   = Results_2ndCompound_others6_CC[14]
                            R_HSaw[t]                   = Results_2ndCompound_others6_CC[15]
                            R_HPulp[t]                  = Results_2ndCompound_others6_CC[16]
                            R_PSaw[t]                   = Results_2ndCompound_others6_CC[17]
                            R_PPulp[t]                  = Results_2ndCompound_others6_CC[18]
                            G_before                    = Results_2ndCompound_others6_CC[19]
                            R_BA                        = Results_2ndCompound_others6_CC[20]
                            ba[t]                       = Results_2ndCompound_others6_CC[21]
                            BGB[t]                      = Results_2ndCompound_others6_CC[22]
                            Tot_co2[t]                  = Results_2ndCompound_others6_CC[23]
                            Tot_biomass[t]              = Results_2ndCompound_others6_CC[24]
                            Total_carbon[t]             = Results_2ndCompound_others6_CC[25]
                            Tot_carbon_stems[t]         = Results_2ndCompound_others6_CC[26]
                            Tot_carbon_roots[t]         = Results_2ndCompound_others6_CC[27]
                            Tot_co2_stems[t]            = Results_2ndCompound_others6_CC[28]
                            Tot_co2_roots[t]            = Results_2ndCompound_others6_CC[29]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 

                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and (len(trees_pine_toDelete4) == 0):  
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
            
            ##[ "High_spruce", "Medium_spruce",  "Low_spruce"] 
            elif CutFirst == "others_spruce":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):          
                        if (t in trees_others) and (len(trees_others_s3_toDelete) != 0):  
                                                           
                            Results_1stCompound_others2_CC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_1stCompound_others2_CC[0]
                            R_vol_birch                 = Results_1stCompound_others2_CC[1]
                            R_vol_others                = Results_1stCompound_others2_CC[2]
                            R_vol_ros                   = Results_1stCompound_others2_CC[3]
                            R_vol_warm                  = Results_1stCompound_others2_CC[4]
                            trees_dict[t]               = Results_1stCompound_others2_CC[5]                            
                            volsum[t]                   = Results_1stCompound_others2_CC[6]
                            vol_spruce[t]               = Results_1stCompound_others2_CC[7]
                            vol_pine[t]                 = Results_1stCompound_others2_CC[8]
                            vol_birch[t]                = Results_1stCompound_others2_CC[9]
                            vol_others[t]               = Results_1stCompound_others2_CC[10]
                            vol_ROS[t]                  = Results_1stCompound_others2_CC[11]
                            vol_warm[t]                 = Results_1stCompound_others2_CC[12]
                            R_SPulp[t]                  = Results_1stCompound_others2_CC[13]
                            R_SSaw[t]                   = Results_1stCompound_others2_CC[14]
                            R_HSaw[t]                   = Results_1stCompound_others2_CC[15]
                            R_HPulp[t]                  = Results_1stCompound_others2_CC[16]
                            R_PSaw[t]                   = Results_1stCompound_others2_CC[17]
                            R_PPulp[t]                  = Results_1stCompound_others2_CC[18] 
                            G_before                    = Results_1stCompound_others2_CC[19]
                            R_BA                        = Results_1stCompound_others2_CC[20]
                            ba[t]                       = Results_1stCompound_others2_CC[21]
                            BGB[t]                      = Results_1stCompound_others2_CC[22]
                            Tot_co2[t]                  = Results_1stCompound_others2_CC[23]
                            Tot_biomass[t]              = Results_1stCompound_others2_CC[24]
                            Total_carbon[t]             = Results_1stCompound_others2_CC[25]
                            Tot_carbon_stems[t]         = Results_1stCompound_others2_CC[26]
                            Tot_carbon_roots[t]         = Results_1stCompound_others2_CC[27]
                            Tot_co2_stems[t]            = Results_1stCompound_others2_CC[28]
                            Tot_co2_roots[t]            = Results_1stCompound_others2_CC[29]
                            trees_others_s3_toDelete.remove(str(t))
                    else:
                        
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.        
                
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):                                           
                        if (t in trees_spruce) and len(trees_others_s3_toDelete) == 0: 
                            
                            Results_Compound_Spruce3_only_CC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed               = Results_Compound_Spruce3_only_CC[0]
                            R_vol_spruce            = Results_Compound_Spruce3_only_CC[1]
                            trees_dict[t]           = Results_Compound_Spruce3_only_CC[2]                           
                            volsum[t]               = Results_Compound_Spruce3_only_CC[3]
                            vol_spruce[t]           = Results_Compound_Spruce3_only_CC[4]
                            vol_pine[t]             = Results_Compound_Spruce3_only_CC[5]
                            vol_birch[t]            = Results_Compound_Spruce3_only_CC[6]
                            vol_others[t]           = Results_Compound_Spruce3_only_CC[7]
                            vol_ROS[t]              = Results_Compound_Spruce3_only_CC[8]
                            vol_warm[t]             = Results_Compound_Spruce3_only_CC[9]
                            R_SPulp[t]              = Results_Compound_Spruce3_only_CC[10]
                            R_SSaw[t]               = Results_Compound_Spruce3_only_CC[11]
                            R_HSaw[t]               = Results_Compound_Spruce3_only_CC[12]
                            R_HPulp[t]              = Results_Compound_Spruce3_only_CC[13]
                            R_PSaw[t]               = Results_Compound_Spruce3_only_CC[14]
                            R_PPulp[t]              = Results_Compound_Spruce3_only_CC[15]
                            G_before                = Results_Compound_Spruce3_only_CC[16]
                            R_BA                    = Results_Compound_Spruce3_only_CC[17]
                            ba[t]                   = Results_Compound_Spruce3_only_CC[18]
                            BGB[t]                  = Results_Compound_Spruce3_only_CC[19]
                            Tot_co2[t]              = Results_Compound_Spruce3_only_CC[20]
                            Tot_biomass[t]          = Results_Compound_Spruce3_only_CC[21]
                            Total_carbon[t]         = Results_Compound_Spruce3_only_CC[22]
                            Tot_carbon_stems[t]     = Results_Compound_Spruce3_only_CC[23]
                            Tot_carbon_roots[t]     = Results_Compound_Spruce3_only_CC[24]
                            Tot_co2_stems[t]        = Results_Compound_Spruce3_only_CC[25]
                            Tot_co2_roots[t]        = Results_Compound_Spruce3_only_CC[26]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        
                for tree in trees:
                    t = tree
                    if (t in trees_pine): 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_pine    = R_vol_pine
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        
            
            #[ "High_spruce", "Medium_spruce",  "Low_spruce"] 
            elif CutFirst == "spruce_others":   
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and (len(trees_spruce_toDelete5) !=0):
                            Results_1stCompound_spruce8_CC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, 
                                                                                         Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                         N_removed, G_before)
                            
                            N_removed                  = Results_1stCompound_spruce8_CC[0]
                            R_vol_spruce               = Results_1stCompound_spruce8_CC[1]
                            trees_dict[t]              = Results_1stCompound_spruce8_CC[2]
                            volsum[t]                  = Results_1stCompound_spruce8_CC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce8_CC[4]
                            vol_pine[t]                = Results_1stCompound_spruce8_CC[5]
                            vol_birch[t]               = Results_1stCompound_spruce8_CC[6]
                            vol_others[t]              = Results_1stCompound_spruce8_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce8_CC[8]
                            vol_warm[t]                = Results_1stCompound_spruce8_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce8_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce8_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce8_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce8_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce8_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce8_CC[15]  
                            G_before                   = Results_1stCompound_spruce8_CC[16]
                            R_BA                       = Results_1stCompound_spruce8_CC[17]
                            ba[t]                      = Results_1stCompound_spruce8_CC[18]
                            BGB[t]                     = Results_1stCompound_spruce8_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce8_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce8_CC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce8_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce8_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce8_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce8_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce8_CC[26]
                            trees_spruce_toDelete5.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and (len(trees_others_s2_toDelete) != 0) and (len(trees_spruce_toDelete5) == 0): 
                            Results_2ndCompound_others2_CC = self.SecondCompound_Others(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, 
                                                                                        Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,R_vol_others,R_vol_ros,R_vol_warm ,
                                                                                        N_removed, G_before)                           
                            N_removed                   = Results_2ndCompound_others2_CC[0]
                            R_vol_birch                 = Results_2ndCompound_others2_CC[1]
                            R_vol_others                = Results_2ndCompound_others2_CC[2]
                            R_vol_ros                   = Results_2ndCompound_others2_CC[3]
                            R_vol_warm                  = Results_2ndCompound_others2_CC[4]
                            trees_dict[t]               = Results_2ndCompound_others2_CC[5]
                            volsum[t]                   = Results_2ndCompound_others2_CC[6]
                            vol_spruce[t]               = Results_2ndCompound_others2_CC[7]
                            vol_pine[t]                 = Results_2ndCompound_others2_CC[8]
                            vol_birch[t]                = Results_2ndCompound_others2_CC[9]
                            vol_others[t]               = Results_2ndCompound_others2_CC[10]
                            vol_ROS[t]                  = Results_2ndCompound_others2_CC[11]
                            vol_warm[t]                 = Results_2ndCompound_others2_CC[12]
                            R_SPulp[t]                  = Results_2ndCompound_others2_CC[13]
                            R_SSaw[t]                   = Results_2ndCompound_others2_CC[14]
                            R_HSaw[t]                   = Results_2ndCompound_others2_CC[15]
                            R_HPulp[t]                  = Results_2ndCompound_others2_CC[16]
                            R_PSaw[t]                   = Results_2ndCompound_others2_CC[17]
                            R_PPulp[t]                  = Results_2ndCompound_others2_CC[18]
                            G_before                    = Results_2ndCompound_others2_CC[19]
                            R_BA                        = Results_2ndCompound_others2_CC[20]
                            ba[t]                       = Results_2ndCompound_others2_CC[21]
                            BGB[t]                      = Results_2ndCompound_others2_CC[22]
                            Tot_co2[t]                  = Results_2ndCompound_others2_CC[23]
                            Tot_biomass[t]              = Results_2ndCompound_others2_CC[24]
                            Total_carbon[t]             = Results_2ndCompound_others2_CC[25]
                            Tot_carbon_stems[t]         = Results_2ndCompound_others2_CC[26]
                            Tot_carbon_roots[t]         = Results_2ndCompound_others2_CC[27]
                            Tot_co2_stems[t]            = Results_2ndCompound_others2_CC[28]
                            Tot_co2_roots[t]            = Results_2ndCompound_others2_CC[29]
                            trees_others_s2_toDelete.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                                                                            
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and (len(trees_spruce_toDelete5) == 0) and (len(trees_others_s2_toDelete) == 0):  

                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_pine    = R_vol_pine
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.                                
        
        elif mic_t == "broadleaf":
            if CutFirst == "spruce_others":   
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and (len(trees_spruce_toDelete6)!=0): 
                            Results_1stCompound_spruce5_CC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                       N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce5_CC[0]
                            R_vol_spruce               = Results_1stCompound_spruce5_CC[1]
                            trees_dict[t]              = Results_1stCompound_spruce5_CC[2]
                            volsum[t]                  = Results_1stCompound_spruce5_CC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce5_CC[4]
                            vol_pine[t]                = Results_1stCompound_spruce5_CC[5]
                            vol_birch[t]               = Results_1stCompound_spruce5_CC[6]
                            vol_others[t]              = Results_1stCompound_spruce5_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce5_CC[8]
                            vol_warm[t]                = Results_1stCompound_spruce5_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce5_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce5_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce5_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce5_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce5_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce5_CC[15]  
                            G_before                   = Results_1stCompound_spruce5_CC[16]
                            R_BA                       = Results_1stCompound_spruce5_CC[17]
                            ba[t]                      = Results_1stCompound_spruce5_CC[18]
                            BGB[t]                     = Results_1stCompound_spruce5_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce5_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce5_CC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce5_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce5_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce5_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce5_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce5_CC[26]
                            trees_spruce_toDelete6.remove(str(t)) 
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and (len(trees_others_s5_toDelete) != 0) and (len(trees_spruce_toDelete6) == 0):   
                            Results_2ndCompound_others3_CC = self.SecondCompound_Others(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                        Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                        R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)                           
                            N_removed                   = Results_2ndCompound_others3_CC[0]
                            R_vol_birch                 = Results_2ndCompound_others3_CC[1]
                            R_vol_others                = Results_2ndCompound_others3_CC[2]
                            R_vol_ros                   = Results_2ndCompound_others3_CC[3]
                            R_vol_warm                  = Results_2ndCompound_others3_CC[4]
                            trees_dict[t]               = Results_2ndCompound_others3_CC[5]
                            volsum[t]                   = Results_2ndCompound_others3_CC[6]
                            vol_spruce[t]               = Results_2ndCompound_others3_CC[7]
                            vol_pine[t]                 = Results_2ndCompound_others3_CC[8]
                            vol_birch[t]                = Results_2ndCompound_others3_CC[9]
                            vol_others[t]               = Results_2ndCompound_others3_CC[10]
                            vol_ROS[t]                  = Results_2ndCompound_others3_CC[11]
                            vol_warm[t]                 = Results_2ndCompound_others3_CC[12]
                            R_SPulp[t]                  = Results_2ndCompound_others3_CC[13]
                            R_SSaw[t]                   = Results_2ndCompound_others3_CC[14]
                            R_HSaw[t]                   = Results_2ndCompound_others3_CC[15]
                            R_HPulp[t]                  = Results_2ndCompound_others3_CC[16]
                            R_PSaw[t]                   = Results_2ndCompound_others3_CC[17]
                            R_PPulp[t]                  = Results_2ndCompound_others3_CC[18]
                            G_before                    = Results_2ndCompound_others3_CC[19]
                            R_BA                        = Results_2ndCompound_others3_CC[20]
                            ba[t]                       = Results_2ndCompound_others3_CC[21]
                            BGB[t]                      = Results_2ndCompound_others3_CC[22]
                            Tot_co2[t]                  = Results_2ndCompound_others3_CC[23]
                            Tot_biomass[t]              = Results_2ndCompound_others3_CC[24]
                            Total_carbon[t]             = Results_2ndCompound_others3_CC[25]
                            Tot_carbon_stems[t]         = Results_2ndCompound_others3_CC[26]
                            Tot_carbon_roots[t]         = Results_2ndCompound_others3_CC[27]
                            Tot_co2_stems[t]            = Results_2ndCompound_others3_CC[28]
                            Tot_co2_roots[t]            = Results_2ndCompound_others3_CC[29]
                            trees_others_s5_toDelete.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                                                                            
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and (len(trees_spruce_toDelete6) == 0) and (len(trees_others_s5_toDelete) == 0):  
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_pine    = R_vol_pine
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
 
            
            ##mic_t == "broadleaf"
            elif CutFirst == "others_spruce":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and len(trees_others_s4_toDelete)!= 0:
                            
                            Results_1stCompound_others3_CC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_1stCompound_others3_CC[0]
                            R_vol_birch                 = Results_1stCompound_others3_CC[1]
                            R_vol_others                = Results_1stCompound_others3_CC[2]
                            R_vol_ros                   = Results_1stCompound_others3_CC[3]
                            R_vol_warm                  = Results_1stCompound_others3_CC[4]
                            trees_dict[t]               = Results_1stCompound_others3_CC[5]
                            volsum[t]                   = Results_1stCompound_others3_CC[6]
                            vol_spruce[t]               = Results_1stCompound_others3_CC[7]
                            vol_pine[t]                 = Results_1stCompound_others3_CC[8]
                            vol_birch[t]                = Results_1stCompound_others3_CC[9]
                            vol_others[t]               = Results_1stCompound_others3_CC[10]
                            vol_ROS[t]                  = Results_1stCompound_others3_CC[11]
                            vol_warm[t]                 = Results_1stCompound_others3_CC[12]
                            R_SPulp[t]                  = Results_1stCompound_others3_CC[13]
                            R_SSaw[t]                   = Results_1stCompound_others3_CC[14]
                            R_HSaw[t]                   = Results_1stCompound_others3_CC[15]
                            R_HPulp[t]                  = Results_1stCompound_others3_CC[16]
                            R_PSaw[t]                   = Results_1stCompound_others3_CC[17]
                            R_PPulp[t]                  = Results_1stCompound_others3_CC[18] 
                            G_before                    = Results_1stCompound_others3_CC[19] 
                            R_BA                        = Results_1stCompound_others3_CC[20]
                            ba[t]                       = Results_1stCompound_others3_CC[21]
                            BGB[t]                      = Results_1stCompound_others3_CC[22]
                            Tot_co2[t]                  = Results_1stCompound_others3_CC[23]
                            Tot_biomass[t]              = Results_1stCompound_others3_CC[24]
                            Total_carbon[t]             = Results_1stCompound_others3_CC[25]
                            Tot_carbon_stems[t]         = Results_1stCompound_others3_CC[26]
                            Tot_carbon_roots[t]         = Results_1stCompound_others3_CC[27]
                            Tot_co2_stems[t]            = Results_1stCompound_others3_CC[28]
                            Tot_co2_roots[t]            = Results_1stCompound_others3_CC[29]
                            trees_others_s4_toDelete.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and len(trees_others_s4_toDelete) == 0: 
                            Results_Compound_Spruce4_only_CC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems,
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed                   = Results_Compound_Spruce4_only_CC[0]
                            R_vol_spruce                = Results_Compound_Spruce4_only_CC[1]
                            trees_dict[t]               = Results_Compound_Spruce4_only_CC[2]
                            volsum[t]                   = Results_Compound_Spruce4_only_CC[3]
                            vol_spruce[t]               = Results_Compound_Spruce4_only_CC[4]
                            vol_pine[t]                 = Results_Compound_Spruce4_only_CC[5]
                            vol_birch[t]                = Results_Compound_Spruce4_only_CC[6]
                            vol_others[t]               = Results_Compound_Spruce4_only_CC[7]
                            vol_ROS[t]                  = Results_Compound_Spruce4_only_CC[8]
                            vol_warm[t]                 = Results_Compound_Spruce4_only_CC[9]
                            R_SPulp[t]                  = Results_Compound_Spruce4_only_CC[10]
                            R_SSaw[t]                   = Results_Compound_Spruce4_only_CC[11]
                            R_HSaw[t]                   = Results_Compound_Spruce4_only_CC[12]
                            R_HPulp[t]                  = Results_Compound_Spruce4_only_CC[13]
                            R_PSaw[t]                   = Results_Compound_Spruce4_only_CC[14]
                            R_PPulp[t]                  = Results_Compound_Spruce4_only_CC[15]
                            G_before                    = Results_Compound_Spruce4_only_CC[16]
                            R_BA                        = Results_Compound_Spruce4_only_CC[17]
                            ba[t]                       = Results_Compound_Spruce4_only_CC[18]
                            BGB[t]                      = Results_Compound_Spruce4_only_CC[19]
                            Tot_co2[t]                  = Results_Compound_Spruce4_only_CC[20]
                            Tot_biomass[t]              = Results_Compound_Spruce4_only_CC[21]
                            Total_carbon[t]             = Results_Compound_Spruce4_only_CC[22]
                            Tot_carbon_stems[t]         = Results_Compound_Spruce4_only_CC[23]
                            Tot_carbon_roots[t]         = Results_Compound_Spruce4_only_CC[24]
                            Tot_co2_stems[t]            = Results_Compound_Spruce4_only_CC[25]
                            Tot_co2_roots[t]            = Results_Compound_Spruce4_only_CC[26]
                    else:
                        
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 
                
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and (len(trees_others_s4_toDelete) == 0):  
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_pine    = R_vol_pine
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.                          

            elif CutFirst == "others_only":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_others:
                            Results_Compound_others_only_CC = self.SecondCompound_Others(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                         R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)                           
                            N_removed                   = Results_Compound_others_only_CC[0]
                            R_vol_birch                 = Results_Compound_others_only_CC[1]
                            R_vol_others                = Results_Compound_others_only_CC[2]
                            R_vol_ros                   = Results_Compound_others_only_CC[3]
                            R_vol_warm                  = Results_Compound_others_only_CC[4]
                            trees_dict[t]               = Results_Compound_others_only_CC[5]
                            volsum[t]                   = Results_Compound_others_only_CC[6]
                            vol_spruce[t]               = Results_Compound_others_only_CC[7]
                            vol_pine[t]                 = Results_Compound_others_only_CC[8]
                            vol_birch[t]                = Results_Compound_others_only_CC[9]
                            vol_others[t]               = Results_Compound_others_only_CC[10]
                            vol_ROS[t]                  = Results_Compound_others_only_CC[11]
                            vol_warm[t]                 = Results_Compound_others_only_CC[12]
                            R_SPulp[t]                  = Results_Compound_others_only_CC[13]
                            R_SSaw[t]                   = Results_Compound_others_only_CC[14]
                            R_HSaw[t]                   = Results_Compound_others_only_CC[15]
                            R_HPulp[t]                  = Results_Compound_others_only_CC[16]
                            R_PSaw[t]                   = Results_Compound_others_only_CC[17]
                            R_PPulp[t]                  = Results_Compound_others_only_CC[18]
                            G_before                    = Results_Compound_others_only_CC[19]
                            R_BA                        = Results_Compound_others_only_CC[20]
                            ba[t]                       = Results_Compound_others_only_CC[21]
                            BGB[t]                      = Results_Compound_others_only_CC[22]
                            Tot_co2[t]                  = Results_Compound_others_only_CC[23]
                            Tot_biomass[t]              = Results_Compound_others_only_CC[24]
                            Total_carbon[t]             = Results_Compound_others_only_CC[25]
                            Tot_carbon_stems[t]         = Results_Compound_others_only_CC[26]
                            Tot_carbon_roots[t]         = Results_Compound_others_only_CC[27]
                            Tot_co2_stems[t]            = Results_Compound_others_only_CC[28]
                            Tot_co2_roots[t]            = Results_Compound_others_only_CC[29]
                                                                      
                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree
                            N_removed     = 0
                            R_vol_spruce  = R_vol_spruce
                            R_vol_pine    = R_vol_pine
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0. 
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 

            ##mic_t == "broadleaf"
            elif CutFirst == "others_spruce_pine":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and len(trees_others_s9_toDelete)!= 0:                                     
                            Results_1stCompound_others8_CC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_1stCompound_others8_CC[0]
                            R_vol_birch                 = Results_1stCompound_others8_CC[1]
                            R_vol_others                = Results_1stCompound_others8_CC[2]
                            R_vol_ros                   = Results_1stCompound_others8_CC[3]
                            R_vol_warm                  = Results_1stCompound_others8_CC[4]
                            trees_dict[t]               = Results_1stCompound_others8_CC[5]
                            volsum[t]                   = Results_1stCompound_others8_CC[6]
                            vol_spruce[t]               = Results_1stCompound_others8_CC[7]
                            vol_pine[t]                 = Results_1stCompound_others8_CC[8]
                            vol_birch[t]                = Results_1stCompound_others8_CC[9]
                            vol_others[t]               = Results_1stCompound_others8_CC[10]
                            vol_ROS[t]                  = Results_1stCompound_others8_CC[11]
                            vol_warm[t]                 = Results_1stCompound_others8_CC[12]
                            R_SPulp[t]                  = Results_1stCompound_others8_CC[13]
                            R_SSaw[t]                   = Results_1stCompound_others8_CC[14]
                            R_HSaw[t]                   = Results_1stCompound_others8_CC[15]
                            R_HPulp[t]                  = Results_1stCompound_others8_CC[16]
                            R_PSaw[t]                   = Results_1stCompound_others8_CC[17]
                            R_PPulp[t]                  = Results_1stCompound_others8_CC[18]
                            G_before                    = Results_1stCompound_others8_CC[19]
                            R_BA                        = Results_1stCompound_others8_CC[20]
                            ba[t]                       = Results_1stCompound_others8_CC[21]
                            BGB[t]                      = Results_1stCompound_others8_CC[22]
                            Tot_co2[t]                  = Results_1stCompound_others8_CC[23]
                            Tot_biomass[t]              = Results_1stCompound_others8_CC[24]
                            Total_carbon[t]             = Results_1stCompound_others8_CC[25]
                            Tot_carbon_stems[t]         = Results_1stCompound_others8_CC[26]
                            Tot_carbon_roots[t]         = Results_1stCompound_others8_CC[27]
                            Tot_co2_stems[t]            = Results_1stCompound_others8_CC[28]
                            Tot_co2_roots[t]            = Results_1stCompound_others8_CC[29]
                            trees_others_s9_toDelete.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and len(trees_others_s9_toDelete) == 0 and len(trees_spruce1_toDelete) != 0: 
                            Results_Compound_Spruce7_only_CC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems,
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed                   = Results_Compound_Spruce7_only_CC[0]
                            R_vol_spruce                = Results_Compound_Spruce7_only_CC[1]
                            trees_dict[t]               = Results_Compound_Spruce7_only_CC[2]
                            volsum[t]                   = Results_Compound_Spruce7_only_CC[3]
                            vol_spruce[t]               = Results_Compound_Spruce7_only_CC[4]
                            vol_pine[t]                 = Results_Compound_Spruce7_only_CC[5]
                            vol_birch[t]                = Results_Compound_Spruce7_only_CC[6]
                            vol_others[t]               = Results_Compound_Spruce7_only_CC[7]
                            vol_ROS[t]                  = Results_Compound_Spruce7_only_CC[8]
                            vol_warm[t]                 = Results_Compound_Spruce7_only_CC[9]
                            R_SPulp[t]                  = Results_Compound_Spruce7_only_CC[10]
                            R_SSaw[t]                   = Results_Compound_Spruce7_only_CC[11]
                            R_HSaw[t]                   = Results_Compound_Spruce7_only_CC[12]
                            R_HPulp[t]                  = Results_Compound_Spruce7_only_CC[13]
                            R_PSaw[t]                   = Results_Compound_Spruce7_only_CC[14]
                            R_PPulp[t]                  = Results_Compound_Spruce7_only_CC[15]
                            G_before                    = Results_Compound_Spruce7_only_CC[16]
                            R_BA                        = Results_Compound_Spruce7_only_CC[17]
                            ba[t]                       = Results_Compound_Spruce7_only_CC[18]
                            BGB[t]                      = Results_Compound_Spruce7_only_CC[19]
                            Tot_co2[t]                  = Results_Compound_Spruce7_only_CC[20]
                            Tot_biomass[t]              = Results_Compound_Spruce7_only_CC[21]
                            Total_carbon[t]             = Results_Compound_Spruce7_only_CC[22]
                            Tot_carbon_stems[t]         = Results_Compound_Spruce7_only_CC[23]
                            Tot_carbon_roots[t]         = Results_Compound_Spruce7_only_CC[24]
                            Tot_co2_stems[t]            = Results_Compound_Spruce7_only_CC[25]
                            Tot_co2_roots[t]            = Results_Compound_Spruce7_only_CC[26]
                            trees_spruce1_toDelete.remove(str(t))
                    else:
                        
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.  
    
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and len(trees_others_s9_toDelete) == 0 and len(trees_spruce1_toDelete) == 0:                 
                            Results_2ndCompound_pine9_CC = self.Compound_pine_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                   N_removed, G_before)
                            
                            N_removed                   = Results_2ndCompound_pine9_CC[0]
                            R_vol_pine                  = Results_2ndCompound_pine9_CC[1]
                            trees_dict[t]               = Results_2ndCompound_pine9_CC[2]
                            volsum[t]                   = Results_2ndCompound_pine9_CC[3]
                            vol_spruce[t]               = Results_2ndCompound_pine9_CC[4]
                            vol_pine[t]                 = Results_2ndCompound_pine9_CC[5]
                            vol_birch[t]                = Results_2ndCompound_pine9_CC[6]
                            vol_others[t]               = Results_2ndCompound_pine9_CC[7]
                            vol_ROS[t]                  = Results_2ndCompound_pine9_CC[8]
                            vol_warm[t]                 = Results_2ndCompound_pine9_CC[9]
                            R_SPulp[t]                  = Results_2ndCompound_pine9_CC[10]
                            R_SSaw[t]                   = Results_2ndCompound_pine9_CC[11]
                            R_HSaw[t]                   = Results_2ndCompound_pine9_CC[12]
                            R_HPulp[t]                  = Results_2ndCompound_pine9_CC[13]
                            R_PSaw[t]                   = Results_2ndCompound_pine9_CC[14]
                            R_PPulp[t]                  = Results_2ndCompound_pine9_CC[15]
                            G_before                    = Results_2ndCompound_pine9_CC[16]
                            R_BA                        = Results_2ndCompound_pine9_CC[17]
                            ba[t]                       = Results_2ndCompound_pine9_CC[18]
                            BGB[t]                      = Results_2ndCompound_pine9_CC[19]
                            Tot_co2[t]                  = Results_2ndCompound_pine9_CC[20]
                            Tot_biomass[t]              = Results_2ndCompound_pine9_CC[21]
                            Total_carbon[t]             = Results_2ndCompound_pine9_CC[22]
                            Tot_carbon_stems[t]         = Results_2ndCompound_pine9_CC[23]
                            Tot_carbon_roots[t]         = Results_2ndCompound_pine9_CC[24]
                            Tot_co2_stems[t]            = Results_2ndCompound_pine9_CC[25]
                            Tot_co2_roots[t]            = Results_2ndCompound_pine9_CC[26]
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.

                        
                        
            ##mic_t == "broadleaf"
            elif CutFirst == "others_pine_spruce":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and len(trees_others_p5_toDelete)!= 0:                                     
                            Results_1stCompound_others7_CC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_1stCompound_others7_CC[0]
                            R_vol_birch                 = Results_1stCompound_others7_CC[1]
                            R_vol_others                = Results_1stCompound_others7_CC[2]
                            R_vol_ros                   = Results_1stCompound_others7_CC[3]
                            R_vol_warm                  = Results_1stCompound_others7_CC[4]
                            trees_dict[t]               = Results_1stCompound_others7_CC[5]
                            volsum[t]                   = Results_1stCompound_others7_CC[6]
                            vol_spruce[t]               = Results_1stCompound_others7_CC[7]
                            vol_pine[t]                 = Results_1stCompound_others7_CC[8]
                            vol_birch[t]                = Results_1stCompound_others7_CC[9]
                            vol_others[t]               = Results_1stCompound_others7_CC[10]
                            vol_ROS[t]                  = Results_1stCompound_others7_CC[11]
                            vol_warm[t]                 = Results_1stCompound_others7_CC[12]
                            R_SPulp[t]                  = Results_1stCompound_others7_CC[13]
                            R_SSaw[t]                   = Results_1stCompound_others7_CC[14]
                            R_HSaw[t]                   = Results_1stCompound_others7_CC[15]
                            R_HPulp[t]                  = Results_1stCompound_others7_CC[16]
                            R_PSaw[t]                   = Results_1stCompound_others7_CC[17]
                            R_PPulp[t]                  = Results_1stCompound_others7_CC[18]
                            G_before                    = Results_1stCompound_others7_CC[19]
                            R_BA                        = Results_1stCompound_others7_CC[20]
                            ba[t]                       = Results_1stCompound_others7_CC[21]
                            BGB[t]                      = Results_1stCompound_others7_CC[22]
                            Tot_co2[t]                  = Results_1stCompound_others7_CC[23]
                            Tot_biomass[t]              = Results_1stCompound_others7_CC[24]
                            Total_carbon[t]             = Results_1stCompound_others7_CC[25]
                            Tot_carbon_stems[t]         = Results_1stCompound_others7_CC[26]
                            Tot_carbon_roots[t]         = Results_1stCompound_others7_CC[27]
                            Tot_co2_stems[t]            = Results_1stCompound_others7_CC[28]
                            Tot_co2_roots[t]            = Results_1stCompound_others7_CC[29]
                            trees_others_p5_toDelete.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and len(trees_others_p5_toDelete) == 0 and len(trees_pine1_toDelete) != 0:                 
                            Results_2ndCompound_pine8_CC = self.Compound_pine_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                   N_removed, G_before)
                            
                            N_removed                   = Results_2ndCompound_pine8_CC[0]
                            R_vol_pine                  = Results_2ndCompound_pine8_CC[1]
                            trees_dict[t]               = Results_2ndCompound_pine8_CC[2]
                            volsum[t]                   = Results_2ndCompound_pine8_CC[3]
                            vol_spruce[t]               = Results_2ndCompound_pine8_CC[4]
                            vol_pine[t]                 = Results_2ndCompound_pine8_CC[5]
                            vol_birch[t]                = Results_2ndCompound_pine8_CC[6]
                            vol_others[t]               = Results_2ndCompound_pine8_CC[7]
                            vol_ROS[t]                  = Results_2ndCompound_pine8_CC[8]
                            vol_warm[t]                 = Results_2ndCompound_pine8_CC[9]
                            R_SPulp[t]                  = Results_2ndCompound_pine8_CC[10]
                            R_SSaw[t]                   = Results_2ndCompound_pine8_CC[11]
                            R_HSaw[t]                   = Results_2ndCompound_pine8_CC[12]
                            R_HPulp[t]                  = Results_2ndCompound_pine8_CC[13]
                            R_PSaw[t]                   = Results_2ndCompound_pine8_CC[14]
                            R_PPulp[t]                  = Results_2ndCompound_pine8_CC[15]
                            G_before                    = Results_2ndCompound_pine8_CC[16]
                            R_BA                        = Results_2ndCompound_pine8_CC[17]
                            ba[t]                       = Results_2ndCompound_pine8_CC[18]
                            BGB[t]                      = Results_2ndCompound_pine8_CC[19]
                            Tot_co2[t]                  = Results_2ndCompound_pine8_CC[20]
                            Tot_biomass[t]              = Results_2ndCompound_pine8_CC[21]
                            Total_carbon[t]             = Results_2ndCompound_pine8_CC[22]
                            Tot_carbon_stems[t]         = Results_2ndCompound_pine8_CC[23]
                            Tot_carbon_roots[t]         = Results_2ndCompound_pine8_CC[24]
                            Tot_co2_stems[t]            = Results_2ndCompound_pine8_CC[25]
                            Tot_co2_roots[t]            = Results_2ndCompound_pine8_CC[26]
                            trees_pine1_toDelete.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and len(trees_others_p5_toDelete) == 0 and len(trees_pine1_toDelete) == 0: 
                            Results_Compound_Spruce6_only_CC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems,
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed                   = Results_Compound_Spruce6_only_CC[0]
                            R_vol_spruce                = Results_Compound_Spruce6_only_CC[1]
                            trees_dict[t]               = Results_Compound_Spruce6_only_CC[2]
                            volsum[t]                   = Results_Compound_Spruce6_only_CC[3]
                            vol_spruce[t]               = Results_Compound_Spruce6_only_CC[4]
                            vol_pine[t]                 = Results_Compound_Spruce6_only_CC[5]
                            vol_birch[t]                = Results_Compound_Spruce6_only_CC[6]
                            vol_others[t]               = Results_Compound_Spruce6_only_CC[7]
                            vol_ROS[t]                  = Results_Compound_Spruce6_only_CC[8]
                            vol_warm[t]                 = Results_Compound_Spruce6_only_CC[9]
                            R_SPulp[t]                  = Results_Compound_Spruce6_only_CC[10]
                            R_SSaw[t]                   = Results_Compound_Spruce6_only_CC[11]
                            R_HSaw[t]                   = Results_Compound_Spruce6_only_CC[12]
                            R_HPulp[t]                  = Results_Compound_Spruce6_only_CC[13]
                            R_PSaw[t]                   = Results_Compound_Spruce6_only_CC[14]
                            R_PPulp[t]                  = Results_Compound_Spruce6_only_CC[15]
                            G_before                    = Results_Compound_Spruce6_only_CC[16]
                            R_BA                        = Results_Compound_Spruce6_only_CC[17]
                            ba[t]                       = Results_Compound_Spruce6_only_CC[18]
                            BGB[t]                      = Results_Compound_Spruce6_only_CC[19]
                            Tot_co2[t]                  = Results_Compound_Spruce6_only_CC[20]
                            Tot_biomass[t]              = Results_Compound_Spruce6_only_CC[21]
                            Total_carbon[t]             = Results_Compound_Spruce6_only_CC[22]
                            Tot_carbon_stems[t]         = Results_Compound_Spruce6_only_CC[23]
                            Tot_carbon_roots[t]         = Results_Compound_Spruce6_only_CC[24]
                            Tot_co2_stems[t]            = Results_Compound_Spruce6_only_CC[25]
                            Tot_co2_roots[t]            = Results_Compound_Spruce6_only_CC[26]
                    else:
                        
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.  
                        
            ##mic_t == "broadleaf"           
            elif CutFirst == "others_pine":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and len(trees_others_p1_toDelete)!= 0:                                     
                            Results_1stCompound_others5_CC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_1stCompound_others5_CC[0]
                            R_vol_birch                 = Results_1stCompound_others5_CC[1]
                            R_vol_others                = Results_1stCompound_others5_CC[2]
                            R_vol_ros                   = Results_1stCompound_others5_CC[3]
                            R_vol_warm                  = Results_1stCompound_others5_CC[4]
                            trees_dict[t]               = Results_1stCompound_others5_CC[5]
                            volsum[t]                   = Results_1stCompound_others5_CC[6]
                            vol_spruce[t]               = Results_1stCompound_others5_CC[7]
                            vol_pine[t]                 = Results_1stCompound_others5_CC[8]
                            vol_birch[t]                = Results_1stCompound_others5_CC[9]
                            vol_others[t]               = Results_1stCompound_others5_CC[10]
                            vol_ROS[t]                  = Results_1stCompound_others5_CC[11]
                            vol_warm[t]                 = Results_1stCompound_others5_CC[12]
                            R_SPulp[t]                  = Results_1stCompound_others5_CC[13]
                            R_SSaw[t]                   = Results_1stCompound_others5_CC[14]
                            R_HSaw[t]                   = Results_1stCompound_others5_CC[15]
                            R_HPulp[t]                  = Results_1stCompound_others5_CC[16]
                            R_PSaw[t]                   = Results_1stCompound_others5_CC[17]
                            R_PPulp[t]                  = Results_1stCompound_others5_CC[18]
                            G_before                    = Results_1stCompound_others5_CC[19]
                            R_BA                        = Results_1stCompound_others5_CC[20]
                            ba[t]                       = Results_1stCompound_others5_CC[21]
                            BGB[t]                      = Results_1stCompound_others5_CC[22]
                            Tot_co2[t]                  = Results_1stCompound_others5_CC[23]
                            Tot_biomass[t]              = Results_1stCompound_others5_CC[24]
                            Total_carbon[t]             = Results_1stCompound_others5_CC[25]
                            Tot_carbon_stems[t]         = Results_1stCompound_others5_CC[26]
                            Tot_carbon_roots[t]         = Results_1stCompound_others5_CC[27]
                            Tot_co2_stems[t]            = Results_1stCompound_others5_CC[28]
                            Tot_co2_roots[t]            = Results_1stCompound_others5_CC[29]
                            trees_others_p1_toDelete.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and len(trees_others_p1_toDelete) == 0:                 
                            Results_2ndCompound_pine5_CC = self.Compound_pine_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                   N_removed, G_before)
                            
                            N_removed                   = Results_2ndCompound_pine5_CC[0]
                            R_vol_pine                  = Results_2ndCompound_pine5_CC[1]
                            trees_dict[t]               = Results_2ndCompound_pine5_CC[2]
                            volsum[t]                   = Results_2ndCompound_pine5_CC[3]
                            vol_spruce[t]               = Results_2ndCompound_pine5_CC[4]
                            vol_pine[t]                 = Results_2ndCompound_pine5_CC[5]
                            vol_birch[t]                = Results_2ndCompound_pine5_CC[6]
                            vol_others[t]               = Results_2ndCompound_pine5_CC[7]
                            vol_ROS[t]                  = Results_2ndCompound_pine5_CC[8]
                            vol_warm[t]                 = Results_2ndCompound_pine5_CC[9]
                            R_SPulp[t]                  = Results_2ndCompound_pine5_CC[10]
                            R_SSaw[t]                   = Results_2ndCompound_pine5_CC[11]
                            R_HSaw[t]                   = Results_2ndCompound_pine5_CC[12]
                            R_HPulp[t]                  = Results_2ndCompound_pine5_CC[13]
                            R_PSaw[t]                   = Results_2ndCompound_pine5_CC[14]
                            R_PPulp[t]                  = Results_2ndCompound_pine5_CC[15]
                            G_before                    = Results_2ndCompound_pine5_CC[16]
                            R_BA                        = Results_2ndCompound_pine5_CC[17]
                            ba[t]                       = Results_2ndCompound_pine5_CC[18]
                            BGB[t]                      = Results_2ndCompound_pine5_CC[19]
                            Tot_co2[t]                  = Results_2ndCompound_pine5_CC[20]
                            Tot_biomass[t]              = Results_2ndCompound_pine5_CC[21]
                            Total_carbon[t]             = Results_2ndCompound_pine5_CC[22]
                            Tot_carbon_stems[t]         = Results_2ndCompound_pine5_CC[23]
                            Tot_carbon_roots[t]         = Results_2ndCompound_pine5_CC[24]
                            Tot_co2_stems[t]            = Results_2ndCompound_pine5_CC[25]
                            Tot_co2_roots[t]            = Results_2ndCompound_pine5_CC[26]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and (len(trees_others_p1_toDelete) == 0):  
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.  
            
            
            ##mic_t == "broadleaf"
            elif CutFirst == "pine_others":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and len(trees_pine_toDelete3)!= 0:                                     
                            Results_1stCompound_pine2_CC = self.firstCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine,
                                                                                   N_removed, G_before)
                            N_removed                  = Results_1stCompound_pine2_CC[0]
                            R_vol_pine                 = Results_1stCompound_pine2_CC[1]
                            trees_dict[t]              = Results_1stCompound_pine2_CC[2]
                            volsum[t]                  = Results_1stCompound_pine2_CC[3]
                            vol_spruce[t]              = Results_1stCompound_pine2_CC[4]
                            vol_pine[t]                = Results_1stCompound_pine2_CC[5]
                            vol_birch[t]               = Results_1stCompound_pine2_CC[6]
                            vol_others[t]              = Results_1stCompound_pine2_CC[7]
                            vol_ROS[t]                 = Results_1stCompound_pine2_CC[8]
                            vol_warm[t]                = Results_1stCompound_pine2_CC[9]
                            R_SPulp[t]                 = Results_1stCompound_pine2_CC[10]
                            R_SSaw[t]                  = Results_1stCompound_pine2_CC[11]
                            R_HSaw[t]                  = Results_1stCompound_pine2_CC[12]
                            R_HPulp[t]                 = Results_1stCompound_pine2_CC[13]
                            R_PSaw[t]                  = Results_1stCompound_pine2_CC[14]
                            R_PPulp[t]                 = Results_1stCompound_pine2_CC[15]
                            G_before                   = Results_1stCompound_pine2_CC[16]
                            R_BA                       = Results_1stCompound_pine2_CC[17]
                            ba[t]                      = Results_1stCompound_pine2_CC[18]
                            BGB[t]                     = Results_1stCompound_pine2_CC[19]
                            Tot_co2[t]                 = Results_1stCompound_pine2_CC[20]
                            Tot_biomass[t]             = Results_1stCompound_pine2_CC[21]
                            Total_carbon[t]            = Results_1stCompound_pine2_CC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_pine2_CC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_pine2_CC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_pine2_CC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_pine2_CC[26]
                            trees_pine_toDelete3.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm      = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.  
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):       
                        if (t in trees_others) and len(trees_pine_toDelete3) == 0:                 
                            Results_2ndCompound_others4_CC = self.SecondCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                        Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,R_vol_others,
                                                                                        R_vol_ros,R_vol_warm ,N_removed, G_before)                        
                            N_removed                   = Results_2ndCompound_others4_CC[0]
                            R_vol_birch                 = Results_2ndCompound_others4_CC[1]
                            R_vol_others                = Results_2ndCompound_others4_CC[2]
                            R_vol_ros                   = Results_2ndCompound_others4_CC[3]
                            R_vol_warm                  = Results_2ndCompound_others4_CC[4]
                            trees_dict[t]               = Results_2ndCompound_others4_CC[5]
                            volsum[t]                   = Results_2ndCompound_others4_CC[6]
                            vol_spruce[t]               = Results_2ndCompound_others4_CC[7]
                            vol_pine[t]                 = Results_2ndCompound_others4_CC[8]
                            vol_birch[t]                = Results_2ndCompound_others4_CC[9]
                            vol_others[t]               = Results_2ndCompound_others4_CC[10]
                            vol_ROS[t]                  = Results_2ndCompound_others4_CC[11]
                            vol_warm[t]                 = Results_2ndCompound_others4_CC[12]
                            R_SPulp[t]                  = Results_2ndCompound_others4_CC[13]
                            R_SSaw[t]                   = Results_2ndCompound_others4_CC[14]
                            R_HSaw[t]                   = Results_2ndCompound_others4_CC[15]
                            R_HPulp[t]                  = Results_2ndCompound_others4_CC[16]
                            R_PSaw[t]                   = Results_2ndCompound_others4_CC[17]
                            R_PPulp[t]                  = Results_2ndCompound_others4_CC[18]
                            G_before                    = Results_2ndCompound_others4_CC[19]
                            R_BA                        = Results_2ndCompound_others4_CC[20]
                            ba[t]                       = Results_2ndCompound_others4_CC[21]
                            BGB[t]                      = Results_2ndCompound_others4_CC[22]
                            Tot_co2[t]                  = Results_2ndCompound_others4_CC[23]
                            Tot_biomass[t]              = Results_2ndCompound_others4_CC[24]
                            Total_carbon[t]             = Results_2ndCompound_others4_CC[25]
                            Tot_carbon_stems[t]         = Results_2ndCompound_others4_CC[26]
                            Tot_carbon_roots[t]         = Results_2ndCompound_others4_CC[27]
                            Tot_co2_stems[t]            = Results_2ndCompound_others4_CC[28]
                            Tot_co2_roots[t]            = Results_2ndCompound_others4_CC[29]
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 

                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and (len(trees_pine_toDelete3) == 0):  
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]                = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]            = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]        = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]       = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t]   = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t]   = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]      = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]      = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                            
        mgt = mgt
        for t in trees:
            try:                
                if trees_dict[t] <= .0001:
                    trees_dict[t] = 0.
            except TypeError:
                ## This part is for the trees which have diameter less than allowance diameterr (check line 5544)
                n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict[t]       = n_tree
                ba[t]               = self.DERIVED_TREES[t].ba
                BGB[t]              = self.DERIVED_TREES[t].BGB
                Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                R_PSaw[t]           = 0.
                R_PPulp[t]          = 0.
                R_HSaw[t]           = 0.
                R_HPulp[t]          = 0.
                R_SSaw[t]           = 0.
                R_SPulp[t]          = 0.

            
            attributes = dict(plot_id = self.DERIVED_TREES[t].plot_id,tree_id = self.DERIVED_TREES[t].tree_id ,tree_sp = self.DERIVED_TREES[t].tree_sp, year = year, dbh = self.DERIVED_TREES[t].dbh , 
                              height = self.DERIVED_TREES[t].height, diameter_class = self.DERIVED_TREES[t].diameter_class, tree_Factor =self.DERIVED_TREES[t].tree_Factor , n_tree = trees_dict[t],
                              SI_spp = self.DERIVED_TREES[t].SI_spp, altitude_m = self.DERIVED_TREES[t].altitude_m, SI_m = self.DERIVED_TREES[t].SI_m, LAT = self.DERIVED_TREES[t].LAT, species = self.DERIVED_TREES[t].species, 
                              t_age =self.DERIVED_TREES[t].t_age , Period = period, yr_since_dead = self.DERIVED_TREES[t].yr_since_dead, Num_DeadTrees = self.DERIVED_TREES[t].Num_DeadTrees, Dom_species = self.DERIVED_TREES[t].Dom_species, BGB = BGB[t], Tot_co2 = Tot_co2[t], 
                              Total_carbon = Total_carbon[t],  Tot_carbon_stems = Tot_carbon_stems[t] , Tot_carbon_roots = Tot_carbon_roots[t], Tot_co2_stems = Tot_co2_stems[t], 
                              Tot_co2_roots = Tot_co2_roots[t], Tot_biomass = Tot_biomass[t], vol_increment = self.DERIVED_TREES[t].vol_increment , dead_volume = self.DERIVED_TREES[t].dead_volume,
                              dead_co2 = self.DERIVED_TREES[t].dead_co2, dead_biomass= self.DERIVED_TREES[t].dead_biomass, dead_C = self.DERIVED_TREES[t].dead_C,  R_SPulp = R_SPulp[t], R_PPulp = R_PPulp[t], R_HPulp = R_HPulp[t], 
                              R_SSaw = R_SSaw[t] , R_PSaw =R_PSaw[t], R_HSaw = R_HSaw[t], Biomass_BAR = self.DERIVED_TREES[t].Biomass_BAR, Biomass_LGR = self.DERIVED_TREES[t].Biomass_LGR, Biomass_RGE5 = self.DERIVED_TREES[t].Biomass_RGE5, 
                              Biomass_RLT5= self.DERIVED_TREES[t].Biomass_RLT5, unwl = self.DERIVED_TREES[t].unwl, ufwl = self.DERIVED_TREES[t].ufwl, ucwl = self.DERIVED_TREES[t].ucwl , temp = self.DERIVED_TREES[t].temp, 
                              coord_x = self.DERIVED_TREES[t].coord_x, coord_y = self.DERIVED_TREES[t].coord_y, volsum = volsum[t], vol_spruce = vol_spruce[t], vol_pine = vol_pine[t], vol_birch = vol_birch[t], vol_others = vol_others[t] , 
                              vol_ROS = vol_ROS[t], vol_warm = vol_warm[t], ba = ba[t], management = mgt)
        
            GrowthModel.TreeGenerator(new_cls_name = t , new_parameters= attributes)

                                                # %%%%%%     fR_SC     %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%        

    def fR_SC(self,R_BGB, R_co2, R_biomass, R_carbon, R_carbon_stems, R_carbon_roots, R_co2_stems, R_co2_roots, R_G, 
              Removed_trees, R_vol_tot, R_vol_spruce, R_vol_pine, R_vol_birch, R_vol_others, R_vol_ros, R_vol_warm,  
              G_b, G_left, mic_tp, year, period, mgt, **kwargs):
        
        """
        This function removes the objects which have met the conditions for clear cut and save small trees and broadleaves
        
        """
        Remove_BGB          =  R_BGB
        Remove_co2          =  R_co2
        Remove_biomass      =  R_biomass 
        Remove_carbon       =  R_carbon
        Remove_carbon_stems =  R_carbon_stems
        Remove_carbon_roots =  R_carbon_roots 
        Remove_co2_stems    =  R_co2_stems
        Remove_co2_roots    =  R_co2_roots
        
        N_removed    = Removed_trees 
        R_BA         = R_G
        R_vol_tot    = R_vol_tot
        R_vol_spruce = R_vol_spruce
        R_vol_pine   = R_vol_pine
        R_vol_birch  = R_vol_birch
        R_vol_others = R_vol_others
        R_vol_ros    = R_vol_ros 
        R_vol_warm   = R_vol_warm
        
        R_v_others     = R_vol_birch + R_vol_others + R_vol_ros + R_vol_warm
        
        
        allowed_diameter = 50
        
        N_removed = Removed_trees  
        BA_left = G_left
        G_before = G_b
        mic_t = mic_tp
              
        trees_spruce, trees_pine, trees_others =[],[],[]
        trees_dict = collections.defaultdict(dict)
        R_SPulp = collections.defaultdict(dict)
        R_SSaw  = collections.defaultdict(dict)
        R_PPulp = collections.defaultdict(dict)
        R_PSaw  = collections.defaultdict(dict)
        R_HPulp = collections.defaultdict(dict)
        R_HSaw  = collections.defaultdict(dict)
        
        
        volsum  = collections.defaultdict(dict)
        vol_spruce  = collections.defaultdict(dict)
        vol_pine  = collections.defaultdict(dict)
        vol_birch  = collections.defaultdict(dict)
        vol_others  = collections.defaultdict(dict)
        vol_ROS  = collections.defaultdict(dict)
        vol_warm  = collections.defaultdict(dict)
        
        BGB                = collections.defaultdict(dict)
        Tot_co2            = collections.defaultdict(dict)
        Tot_biomass        = collections.defaultdict(dict)
        Total_carbon       = collections.defaultdict(dict)
        Tot_carbon_stems   = collections.defaultdict(dict)
        Tot_carbon_roots   = collections.defaultdict(dict)
        Tot_co2_stems      = collections.defaultdict(dict)
        Tot_co2_roots      = collections.defaultdict(dict)
        
        ba = collections.defaultdict(dict)
                
               
        # This part will determine the type of species for cutting
        trees = [k for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].n_tree != 0]

        V_sum = sum([(self.DERIVED_TREES[k].volsum + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys()])
        V_spruce = sum([(self.DERIVED_TREES[k].vol_spruce + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_pine = sum([(self.DERIVED_TREES[k].vol_pine + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_birch = sum([(self.DERIVED_TREES[k].vol_birch + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])  
        V_other = sum([(self.DERIVED_TREES[k].vol_others + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_ROS = sum([(self.DERIVED_TREES[k].vol_ROS + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])
        V_warm =  sum([(self.DERIVED_TREES[k].vol_warm + self.DERIVED_TREES[k].vol_increment) for k in self.DERIVED_TREES.keys() if (self.DERIVED_TREES[k].n_tree != 0)])        
        
        V_others = V_birch + V_other + V_ROS + V_warm

        print(R_vol_tot, V_spruce, V_pine, V_others)
        
        # N_spruce = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "spruce" ])
        # N_pine = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "scots_pine" ])
        # N_birch = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "birch" ]) 
        # N_other = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "other_broadleaves" ])
        # N_ROS = sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "ROS" ])
        # N_warm =  sum([GrowthModel.DERIVED_TREES[k].n_tree for k in GrowthModel.DERIVED_TREES.keys() if GrowthModel.DERIVED_TREES[k].species == "warm"])        
        
        # N_others = N_birch + N_other + N_ROS + N_warm
        
        Scenario_pine_SC         = ["spruce_some", "spruce_pine", "spruce_only", "spruce_others_pine", "others_pine", "others_only", "spruce_others", "others_spruce", "pine_only"]
        
        
        for k in trees:
            if GrowthModel.DERIVED_TREES[k].dbh >= allowed_diameter:
                if GrowthModel.DERIVED_TREES[k].species == "spruce" :
                    trees_spruce.append(k)                
                elif GrowthModel.DERIVED_TREES[k].species == "scots_pine" :
                    trees_pine.append(k)                    
                elif (GrowthModel.DERIVED_TREES[k].species == "birch") :
                    trees_others.append(k)
                elif (GrowthModel.DERIVED_TREES[k].species == "other_broadleaves") :
                    trees_others.append(k)
                elif (GrowthModel.DERIVED_TREES[k].species == "ROS") :
                    trees_others.append(k)
                elif (GrowthModel.DERIVED_TREES[k].species == "warm") :
                    trees_others.append(k)
        
        # this part difines which trees should not be cut
        CutFirst = ""
                    
        if (mic_t == "High_pine") or (mic_t == "Medium_pine"):

            if R_vol_tot <= (V_spruce + V_pine) and (V_others < 1) and (V_spruce >= 1): # case1
                
                if (R_vol_tot <= V_pine) and (R_vol_tot < V_spruce) and (V_pine < V_spruce) and (R_vol_tot != V_spruce):
                    CutFirst = Scenario_pine_SC[0]
                elif (R_vol_tot < V_pine) and (R_vol_tot < V_spruce) and (V_pine > V_spruce) and (R_vol_tot != V_spruce):
                    CutFirst = Scenario_pine_SC[0]
                
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_spruce) and (V_pine >= V_spruce) and (V_pine >= 1):
                    CutFirst = Scenario_pine_SC[1]
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_spruce) and (V_spruce > V_pine ) and (V_pine >= 1):
                    CutFirst = Scenario_pine_SC[1]   
                    
                elif (R_vol_tot < V_pine) and (R_vol_tot > V_spruce):
                     CutFirst = Scenario_pine_SC[1]
                elif (R_vol_tot > V_pine) and (R_vol_tot < V_spruce):
                     CutFirst = Scenario_pine_SC[0] 
                elif (R_vol_tot == V_pine) and (R_vol_tot > V_spruce) and (V_pine >= 1):
                    CutFirst = Scenario_pine_SC[1]
                elif (R_vol_tot == V_spruce) and (R_vol_tot >= V_pine):
                    CutFirst = Scenario_pine_SC[2]
                elif (R_vol_tot > V_spruce) and (R_vol_tot != V_pine) and (V_spruce <= V_pine) and (V_pine >= 1):
                    CutFirst = Scenario_pine_SC[1]
                elif (R_vol_tot > V_pine) and (R_vol_tot != V_spruce) and (V_pine <= V_spruce) and (V_pine >= 1):
                    CutFirst = Scenario_pine_SC[1]
                    
            elif R_vol_tot <= (V_others + V_pine) and (V_spruce < 1) and (V_others >= 1): # case2
                
                if (R_vol_tot <= V_pine) and (R_vol_tot < V_others) and (V_pine < V_others):
                    CutFirst = Scenario_pine_SC[5]
                elif (R_vol_tot < V_pine) and (R_vol_tot < V_others) and (V_pine > V_others):
                    CutFirst = Scenario_pine_SC[5]
                
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_others) and (V_pine >= V_others) and (V_pine >= 1):
                    CutFirst = Scenario_pine_SC[4]
                elif (R_vol_tot > V_pine) and (R_vol_tot > V_others) and (V_others > V_pine ) and (V_pine >= 1):
                    CutFirst = Scenario_pine_SC[4] 
                    
                elif (R_vol_tot < V_pine) and (R_vol_tot > V_others):
                     CutFirst = Scenario_pine_SC[4]
                elif (R_vol_tot > V_pine) and (R_vol_tot < V_others):
                     CutFirst = Scenario_pine_SC[5]
            
            elif R_vol_tot <= (V_others + V_spruce) and (V_spruce >= 1)  and (V_others >= 1): # case3
                
                if (R_vol_tot > V_spruce) and (R_vol_tot > V_others) and (V_spruce >= V_others):
                    CutFirst = Scenario_pine_SC[6]
                elif (R_vol_tot > V_spruce) and (R_vol_tot > V_others) and (V_others > V_spruce ):
                    CutFirst = Scenario_pine_SC[7]
                    
            elif R_vol_tot <= (V_spruce + V_others + V_pine) and (V_spruce < 1)  and (V_others < 1): # case4
                CutFirst = Scenario_pine_SC[8]
            
            elif R_vol_tot > (V_spruce + V_others) and (V_spruce >= 1)  and (V_others >= 1): # case5
                CutFirst = Scenario_pine_SC[3] 
            
            elif R_vol_tot > (V_spruce + V_others) and (V_spruce < 1)  and (V_others >= 1): # case6
                CutFirst = Scenario_pine_SC[4]
                
            elif R_vol_tot > (V_spruce + V_others) and (V_spruce >= 1)  and (V_others < 1): # case6
                CutFirst = Scenario_pine_SC[1]                
          
        # this list will be used for updating the objects
        
        SC_trees_spruce_toDelete1   = trees_spruce.copy()
        SC_trees_spruce_toDelete2   = trees_spruce.copy()
        SC_trees_spruce_toDelete8   = trees_spruce.copy()        
        SC_trees_spruce_toDelete3   = trees_spruce.copy()
        SC_trees_spruce_toDelete4   = trees_spruce.copy()
        
        SC_trees_others_s1_toDelete = trees_others.copy()
        SC_trees_others_s6_toDelete = trees_others.copy()
        SC_trees_others_s8_toDelete = trees_others.copy()
        SC_trees_others_p2_toDelete = trees_others.copy()
        

        SC_trees_pine_toDelete1     = trees_pine.copy()
        SC_trees_pine_toDelete2     = trees_pine.copy()


        
        if (mic_t == "High_pine") or (mic_t == "Medium_pine"):   
            if (CutFirst ==  "spruce_pine"):
                for tree in trees:
                    t= tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and (len(SC_trees_spruce_toDelete1) != 0): 
                            Results_1stCompound_spruce1_SC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                       N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce1_SC[0]
                            R_vol_spruce               = Results_1stCompound_spruce1_SC[1]
                            trees_dict[t]              = Results_1stCompound_spruce1_SC[2]
                            volsum[t]                  = Results_1stCompound_spruce1_SC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce1_SC[4] 
                            vol_pine[t]                = Results_1stCompound_spruce1_SC[5]
                            vol_birch[t]               = Results_1stCompound_spruce1_SC[6]
                            vol_others[t]              = Results_1stCompound_spruce1_SC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce1_SC[8]
                            vol_warm[t]                = Results_1stCompound_spruce1_SC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce1_SC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce1_SC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce1_SC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce1_SC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce1_SC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce1_SC[15]
                            G_before                   = Results_1stCompound_spruce1_SC[16]
                            R_BA                       = Results_1stCompound_spruce1_SC[17]
                            ba[t]                      = Results_1stCompound_spruce1_SC[18]
                            BGB[t]                     = Results_1stCompound_spruce1_SC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce1_SC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce1_SC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce1_SC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce1_SC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce1_SC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce1_SC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce1_SC[26]
                            SC_trees_spruce_toDelete1.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine)  and len(SC_trees_spruce_toDelete1) == 0: 
                            Results_2ndCompound_pine4_SC = self.LastCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                  Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine, 
                                                                                  N_removed, G_before)
                            N_removed               = Results_2ndCompound_pine4_SC[0]
                            R_vol_pine              = Results_2ndCompound_pine4_SC[1]
                            trees_dict[t]           = Results_2ndCompound_pine4_SC[2]
                            volsum[t]               = Results_2ndCompound_pine4_SC[3]
                            vol_spruce[t]           = Results_2ndCompound_pine4_SC[4]
                            vol_pine[t]             = Results_2ndCompound_pine4_SC[5]
                            vol_birch[t]            = Results_2ndCompound_pine4_SC[6]
                            vol_others[t]           = Results_2ndCompound_pine4_SC[7]
                            vol_ROS[t]              = Results_2ndCompound_pine4_SC[8]
                            vol_warm[t]             = Results_2ndCompound_pine4_SC[9]
                            R_SPulp[t]              = Results_2ndCompound_pine4_SC[10]
                            R_SSaw[t]               = Results_2ndCompound_pine4_SC[11]
                            R_HSaw[t]               = Results_2ndCompound_pine4_SC[12]
                            R_HPulp[t]              = Results_2ndCompound_pine4_SC[13]
                            R_PSaw[t]               = Results_2ndCompound_pine4_SC[14]
                            R_PPulp[t]              = Results_2ndCompound_pine4_SC[15]
                            G_before                = Results_2ndCompound_pine4_SC[16]
                            R_BA                    = Results_2ndCompound_pine4_SC[17]
                            ba[t]                   = Results_2ndCompound_pine4_SC[18]
                            BGB[t]                  = Results_2ndCompound_pine4_SC[19]
                            Tot_co2[t]              = Results_2ndCompound_pine4_SC[20]
                            Tot_biomass[t]          = Results_2ndCompound_pine4_SC[21]
                            Total_carbon[t]         = Results_2ndCompound_pine4_SC[22]
                            Tot_carbon_stems[t]     = Results_2ndCompound_pine4_SC[23]
                            Tot_carbon_roots[t]     = Results_2ndCompound_pine4_SC[24]
                            Tot_co2_stems[t]        = Results_2ndCompound_pine4_SC[25]
                            Tot_co2_roots[t]        = Results_2ndCompound_pine4_SC[26]
    
                    else:
                        n_tree = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 

                                
                for t in trees:
                    if (t in trees_others)  and (len(SC_trees_spruce_toDelete1) == 0): 
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0. 
            
            ##mic_t == "High_pine" 
            elif CutFirst == "others_only":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_others:
                            Results_Compound_others2_only_CC = self.SecondCompound_Others(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                         R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)                           
                            N_removed                   = Results_Compound_others2_only_CC[0]
                            R_vol_birch                 = Results_Compound_others2_only_CC[1]
                            R_vol_others                = Results_Compound_others2_only_CC[2]
                            R_vol_ros                   = Results_Compound_others2_only_CC[3]
                            R_vol_warm                  = Results_Compound_others2_only_CC[4]
                            trees_dict[t]               = Results_Compound_others2_only_CC[5]
                            volsum[t]                   = Results_Compound_others2_only_CC[6]
                            vol_spruce[t]               = Results_Compound_others2_only_CC[7]
                            vol_pine[t]                 = Results_Compound_others2_only_CC[8]
                            vol_birch[t]                = Results_Compound_others2_only_CC[9]
                            vol_others[t]               = Results_Compound_others2_only_CC[10]
                            vol_ROS[t]                  = Results_Compound_others2_only_CC[11]
                            vol_warm[t]                 = Results_Compound_others2_only_CC[12]
                            R_SPulp[t]                  = Results_Compound_others2_only_CC[13]
                            R_SSaw[t]                   = Results_Compound_others2_only_CC[14]
                            R_HSaw[t]                   = Results_Compound_others2_only_CC[15]
                            R_HPulp[t]                  = Results_Compound_others2_only_CC[16]
                            R_PSaw[t]                   = Results_Compound_others2_only_CC[17]
                            R_PPulp[t]                  = Results_Compound_others2_only_CC[18]
                            G_before                    = Results_Compound_others2_only_CC[19]
                            R_BA                        = Results_Compound_others2_only_CC[20]
                            ba[t]                       = Results_Compound_others2_only_CC[21]
                            BGB[t]                      = Results_Compound_others2_only_CC[22]
                            Tot_co2[t]                  = Results_Compound_others2_only_CC[23]
                            Tot_biomass[t]              = Results_Compound_others2_only_CC[24]
                            Total_carbon[t]             = Results_Compound_others2_only_CC[25]
                            Tot_carbon_stems[t]         = Results_Compound_others2_only_CC[26]
                            Tot_carbon_roots[t]         = Results_Compound_others2_only_CC[27]
                            Tot_co2_stems[t]            = Results_Compound_others2_only_CC[28]
                            Tot_co2_roots[t]            = Results_Compound_others2_only_CC[29]
                                                                      
                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree
                            N_removed     = 0
                            R_vol_spruce  = R_vol_spruce
                            R_vol_pine    = R_vol_pine
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0. 
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.   
            
            ##mic_t == "High_pine"
            elif (CutFirst == "pine_only"):
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_pine:
                            Results_1Compound_pine1_only_SC = self.Compound_pine_only(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                     Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                     N_removed, G_before)
                            N_removed               = Results_1Compound_pine1_only_SC[0]
                            R_vol_pine              = Results_1Compound_pine1_only_SC[1]
                            trees_dict[t]           = Results_1Compound_pine1_only_SC[2]
                            volsum[t]               = Results_1Compound_pine1_only_SC[3]
                            vol_spruce[t]           = Results_1Compound_pine1_only_SC[4]
                            vol_pine[t]             = Results_1Compound_pine1_only_SC[5]
                            vol_birch[t]            = Results_1Compound_pine1_only_SC[6]
                            vol_others[t]           = Results_1Compound_pine1_only_SC[7]
                            vol_ROS[t]              = Results_1Compound_pine1_only_SC[8]
                            vol_warm[t]             = Results_1Compound_pine1_only_SC[9]
                            R_SPulp[t]              = Results_1Compound_pine1_only_SC[10]
                            R_SSaw[t]               = Results_1Compound_pine1_only_SC[11]
                            R_HSaw[t]               = Results_1Compound_pine1_only_SC[12]
                            R_HPulp[t]              = Results_1Compound_pine1_only_SC[13]
                            R_PSaw[t]               = Results_1Compound_pine1_only_SC[14]
                            R_PPulp[t]              = Results_1Compound_pine1_only_SC[15]
                            G_before                = Results_1Compound_pine1_only_SC[16]
                            R_BA                    = Results_1Compound_pine1_only_SC[17]
                            ba[t]                   = Results_1Compound_pine1_only_SC[18]
                            BGB[t]                  = Results_1Compound_pine1_only_SC[19]
                            Tot_co2[t]              = Results_1Compound_pine1_only_SC[20]
                            Tot_biomass[t]          = Results_1Compound_pine1_only_SC[21]
                            Total_carbon[t]         = Results_1Compound_pine1_only_SC[22]
                            Tot_carbon_stems[t]     = Results_1Compound_pine1_only_SC[23]
                            Tot_carbon_roots[t]     = Results_1Compound_pine1_only_SC[24]
                            Tot_co2_stems[t]        = Results_1Compound_pine1_only_SC[25]
                            Tot_co2_roots[t]        = Results_1Compound_pine1_only_SC[26]
                                                                      
                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree
                            N_removed     = 0
                            R_vol_spruce  = R_vol_spruce
                            R_vol_birch   = R_vol_birch
                            R_vol_others  = R_vol_others
                            R_vol_ros     = R_vol_ros
                            R_vol_warm    = R_vol_warm
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0. 
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                        
                        
            ##mic_t == "High_pine"                                         
            elif CutFirst == "others_pine":
                
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):                                                
                        if (t in trees_others) and (len(SC_trees_others_p2_toDelete) != 0):    
                            Results_1stCompound_others1_SC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed               = Results_1stCompound_others1_SC[0]
                            R_vol_birch             = Results_1stCompound_others1_SC[1]
                            R_vol_others            = Results_1stCompound_others1_SC[2]
                            R_vol_ros               = Results_1stCompound_others1_SC[3]
                            R_vol_warm              = Results_1stCompound_others1_SC[4]
                            trees_dict[t]           = Results_1stCompound_others1_SC[5]
                            volsum[t]               = Results_1stCompound_others1_SC[6]
                            vol_spruce[t]           = Results_1stCompound_others1_SC[7]
                            vol_pine[t]             = Results_1stCompound_others1_SC[8]
                            vol_birch[t]            = Results_1stCompound_others1_SC[9]
                            vol_others[t]           = Results_1stCompound_others1_SC[10]
                            vol_ROS[t]              = Results_1stCompound_others1_SC[11]
                            vol_warm[t]             = Results_1stCompound_others1_SC[12]
                            R_SPulp[t]              = Results_1stCompound_others1_SC[13]
                            R_SSaw[t]               = Results_1stCompound_others1_SC[14]
                            R_HSaw[t]               = Results_1stCompound_others1_SC[15]
                            R_HPulp[t]              = Results_1stCompound_others1_SC[16]
                            R_PSaw[t]               = Results_1stCompound_others1_SC[17]
                            R_PPulp[t]              = Results_1stCompound_others1_SC[18]
                            G_before                = Results_1stCompound_others1_SC[19]
                            R_BA                    = Results_1stCompound_others1_SC[20]
                            ba[t]                   = Results_1stCompound_others1_SC[21]
                            BGB[t]                  = Results_1stCompound_others1_SC[22]
                            Tot_co2[t]              = Results_1stCompound_others1_SC[23]
                            Tot_biomass[t]          = Results_1stCompound_others1_SC[24]
                            Total_carbon[t]         = Results_1stCompound_others1_SC[25]
                            Tot_carbon_stems[t]     = Results_1stCompound_others1_SC[26]
                            Tot_carbon_roots[t]     = Results_1stCompound_others1_SC[27]
                            Tot_co2_stems[t]        = Results_1stCompound_others1_SC[28]
                            Tot_co2_roots[t]        = Results_1stCompound_others1_SC[29]
                            SC_trees_others_p2_toDelete.remove(str(t))
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                RR = []                
                for tree in trees:
                    t = tree                     
                    if (G_before > BA_left):                        
                        if (t in trees_pine) and len(SC_trees_others_p2_toDelete) == 0 and len(SC_trees_pine_toDelete1) != 0:
                            
                            Results_2ndCompound_pine1_SC = self.Compound_pine_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine ,
                                                                                   N_removed, G_before)
                            
                            N_removed               = Results_2ndCompound_pine1_SC[0]
                            R_vol_pine              = Results_2ndCompound_pine1_SC[1]
                            trees_dict[t]           = Results_2ndCompound_pine1_SC[2]
                            volsum[t]               = Results_2ndCompound_pine1_SC[3]
                            vol_spruce[t]           = Results_2ndCompound_pine1_SC[4]
                            vol_pine[t]             = Results_2ndCompound_pine1_SC[5]
                            vol_birch[t]            = Results_2ndCompound_pine1_SC[6]
                            vol_others[t]           = Results_2ndCompound_pine1_SC[7]
                            vol_ROS[t]              = Results_2ndCompound_pine1_SC[8]
                            vol_warm[t]             = Results_2ndCompound_pine1_SC[9]
                            R_SPulp[t]              = Results_2ndCompound_pine1_SC[10]
                            R_SSaw[t]               = Results_2ndCompound_pine1_SC[11]
                            R_HSaw[t]               = Results_2ndCompound_pine1_SC[12]
                            R_HPulp[t]              = Results_2ndCompound_pine1_SC[13]
                            R_PSaw[t]               = Results_2ndCompound_pine1_SC[14]
                            R_PPulp[t]              = Results_2ndCompound_pine1_SC[15]
                            G_before                = Results_2ndCompound_pine1_SC[16]
                            R_BA                    = Results_2ndCompound_pine1_SC[17]
                            ba[t]                   = Results_2ndCompound_pine1_SC[18]
                            BGB[t]                  = Results_2ndCompound_pine1_SC[19]
                            Tot_co2[t]              = Results_2ndCompound_pine1_SC[20]
                            Tot_biomass[t]          = Results_2ndCompound_pine1_SC[21]
                            Total_carbon[t]         = Results_2ndCompound_pine1_SC[22]
                            Tot_carbon_stems[t]     = Results_2ndCompound_pine1_SC[23]
                            Tot_carbon_roots[t]     = Results_2ndCompound_pine1_SC[24]
                            Tot_co2_stems[t]        = Results_2ndCompound_pine1_SC[25]
                            Tot_co2_roots[t]        = Results_2ndCompound_pine1_SC[26]
                            SC_trees_pine_toDelete1.remove(str(t))
                    else:
                        
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                            
                for tree in trees:
                    t = tree
                    if (t in trees_spruce) and len(SC_trees_others_p2_toDelete) == 0 and len(SC_trees_pine_toDelete1) == 0: 
                        
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree 
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.  

                                                           
            elif CutFirst ==  "spruce_some":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_spruce:
                            Results_Compound_Spruce1_SC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                    Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                    N_removed, G_before)
                            N_removed               = Results_Compound_Spruce1_SC[0]
                            R_vol_spruce            = Results_Compound_Spruce1_SC[1]
                            trees_dict[t]           = Results_Compound_Spruce1_SC[2]
                            volsum[t]               = Results_Compound_Spruce1_SC[3]
                            vol_spruce[t]           = Results_Compound_Spruce1_SC[4]
                            vol_pine[t]             = Results_Compound_Spruce1_SC[5]
                            vol_birch[t]            = Results_Compound_Spruce1_SC[6]
                            vol_others[t]           = Results_Compound_Spruce1_SC[7]
                            vol_ROS[t]              = Results_Compound_Spruce1_SC[8]
                            vol_warm[t]             = Results_Compound_Spruce1_SC[9]
                            R_SPulp[t]              = Results_Compound_Spruce1_SC[10]
                            R_SSaw[t]               = Results_Compound_Spruce1_SC[11]
                            R_HSaw[t]               = Results_Compound_Spruce1_SC[12]
                            R_HPulp[t]              = Results_Compound_Spruce1_SC[13]
                            R_PSaw[t]               = Results_Compound_Spruce1_SC[14]
                            R_PPulp[t]              = Results_Compound_Spruce1_SC[15]
                            G_before                = Results_Compound_Spruce1_SC[16]
                            R_BA                    = Results_Compound_Spruce1_SC[17]
                            ba[t]                   = Results_Compound_Spruce1_SC[18]
                            BGB[t]                  = Results_Compound_Spruce1_SC[19]
                            Tot_co2[t]              = Results_Compound_Spruce1_SC[20]
                            Tot_biomass[t]          = Results_Compound_Spruce1_SC[21]
                            Total_carbon[t]         = Results_Compound_Spruce1_SC[22]
                            Tot_carbon_stems[t]     = Results_Compound_Spruce1_SC[23]
                            Tot_carbon_roots[t]     = Results_Compound_Spruce1_SC[24]
                            Tot_co2_stems[t]        = Results_Compound_Spruce1_SC[25]
                            Tot_co2_roots[t]        = Results_Compound_Spruce1_SC[26]

                    else:
                       
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
            
            #mic_t == "High_pine"
            elif (CutFirst ==  "spruce_only"):
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if t in trees_spruce:
                            Results_Compound_Spruce1_only_SC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed               = Results_Compound_Spruce1_only_SC[0]
                            R_vol_spruce            = Results_Compound_Spruce1_only_SC[1]
                            trees_dict[t]           = Results_Compound_Spruce1_only_SC[2]
                            volsum[t]               = Results_Compound_Spruce1_only_SC[3]
                            vol_spruce[t]           = Results_Compound_Spruce1_only_SC[4]
                            vol_pine[t]             = Results_Compound_Spruce1_only_SC[5]
                            vol_birch[t]            = Results_Compound_Spruce1_only_SC[6]
                            vol_others[t]           = Results_Compound_Spruce1_only_SC[7]
                            vol_ROS[t]              = Results_Compound_Spruce1_only_SC[8]
                            vol_warm[t]             = Results_Compound_Spruce1_only_SC[9]
                            R_SPulp[t]              = Results_Compound_Spruce1_only_SC[10]
                            R_SSaw[t]               = Results_Compound_Spruce1_only_SC[11]
                            R_HSaw[t]               = Results_Compound_Spruce1_only_SC[12]
                            R_HPulp[t]              = Results_Compound_Spruce1_only_SC[13]
                            R_PSaw[t]               = Results_Compound_Spruce1_only_SC[14]
                            R_PPulp[t]              = Results_Compound_Spruce1_only_SC[15]
                            G_before                = Results_Compound_Spruce1_only_SC[16]
                            R_BA                    = Results_Compound_Spruce1_only_SC[17]
                            ba[t]                   = Results_Compound_Spruce1_only_SC[18]
                            BGB[t]                  = Results_Compound_Spruce1_only_SC[19]
                            Tot_co2[t]              = Results_Compound_Spruce1_only_SC[20]
                            Tot_biomass[t]          = Results_Compound_Spruce1_only_SC[21]
                            Total_carbon[t]         = Results_Compound_Spruce1_only_SC[22]
                            Tot_carbon_stems[t]     = Results_Compound_Spruce1_only_SC[23]
                            Tot_carbon_roots[t]     = Results_Compound_Spruce1_only_SC[24]
                            Tot_co2_stems[t]        = Results_Compound_Spruce1_only_SC[25]
                            Tot_co2_roots[t]        = Results_Compound_Spruce1_only_SC[26]

                                                                      
                        else:
                            n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                            trees_dict[t] = n_tree
                            N_removed     = 0
                            R_vol_pine    = R_vol_pine
                            R_vol_birch   = R_vol_birch
                            R_vol_others  = R_vol_others
                            R_vol_ros     = R_vol_ros
                            R_vol_warm    = R_vol_warm
                            G_before      = G_before
                            R_BA          = R_BA
                            ba[t]         = self.DERIVED_TREES[t].ba
                            BGB[t]              = self.DERIVED_TREES[t].BGB
                            Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                            Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                            Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                            Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                            Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                            Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                            Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                            volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                            vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                            vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                            vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                            vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                            vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                            vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                            R_HSaw[t]     = 0.
                            R_HPulp[t]    = 0.
                            R_PSaw[t]     = 0.
                            R_PPulp[t]    = 0. 
                            R_SSaw[t]     = 0.
                            R_SPulp[t]    = 0.
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                     
                        
              
            elif (CutFirst ==  "spruce_others_pine"):
                for tree in trees:
                    t= tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and (len(SC_trees_spruce_toDelete2) !=0):                               
                            Results_1stCompound_spruce2_SC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                       N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce2_SC[0]
                            R_vol_spruce               = Results_1stCompound_spruce2_SC[1]
                            trees_dict[t]              = Results_1stCompound_spruce2_SC[2]
                            volsum[t]                  = Results_1stCompound_spruce2_SC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce2_SC[4]
                            vol_pine[t]                = Results_1stCompound_spruce2_SC[5]
                            vol_birch[t]               = Results_1stCompound_spruce2_SC[6]
                            vol_others[t]              = Results_1stCompound_spruce2_SC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce2_SC[8]
                            vol_warm[t]                = Results_1stCompound_spruce2_SC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce2_SC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce2_SC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce2_SC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce2_SC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce2_SC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce2_SC[15]
                            G_before                   = Results_1stCompound_spruce2_SC[16]
                            R_BA                       = Results_1stCompound_spruce2_SC[17]
                            ba[t]                      = Results_1stCompound_spruce2_SC[18]
                            BGB[t]                     = Results_1stCompound_spruce2_SC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce2_SC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce2_SC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce2_SC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce2_SC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce2_SC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce2_SC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce2_SC[26]
                            SC_trees_spruce_toDelete2.remove(str(t))
                                 
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                                                    
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):              
                        if (t in trees_others) and (len(SC_trees_spruce_toDelete2) == 0) and (len(SC_trees_others_s1_toDelete) != 0):  
                            Results_MCompound_others1_SC = self.MiddleCompound_Others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                      Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,R_vol_others,
                                                                                      R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed               = Results_MCompound_others1_SC[0]
                            R_vol_birch             = Results_MCompound_others1_SC[1]
                            R_vol_others            = Results_MCompound_others1_SC[2]
                            R_vol_ros               = Results_MCompound_others1_SC[3]
                            R_vol_warm              = Results_MCompound_others1_SC[4]
                            trees_dict[t]           = Results_MCompound_others1_SC[5]
                            volsum[t]               = Results_MCompound_others1_SC[6]
                            vol_spruce[t]           = Results_MCompound_others1_SC[7]
                            vol_pine[t]             = Results_MCompound_others1_SC[8]
                            vol_birch[t]            = Results_MCompound_others1_SC[9]
                            vol_others[t]           = Results_MCompound_others1_SC[10]
                            vol_ROS[t]              = Results_MCompound_others1_SC[11]
                            vol_warm[t]             = Results_MCompound_others1_SC[12]
                            R_SPulp[t]              = Results_MCompound_others1_SC[13]
                            R_SSaw[t]               = Results_MCompound_others1_SC[14]
                            R_HSaw[t]               = Results_MCompound_others1_SC[15]
                            R_HPulp[t]              = Results_MCompound_others1_SC[16]
                            R_PSaw[t]               = Results_MCompound_others1_SC[17]
                            R_PPulp[t]              = Results_MCompound_others1_SC[18]
                            G_before                = Results_MCompound_others1_SC[19]
                            R_BA                    = Results_MCompound_others1_SC[20]
                            ba[t]                   = Results_MCompound_others1_SC[21]
                            BGB[t]                  = Results_MCompound_others1_SC[22]
                            Tot_co2[t]              = Results_MCompound_others1_SC[23]
                            Tot_biomass[t]          = Results_MCompound_others1_SC[24]
                            Total_carbon[t]         = Results_MCompound_others1_SC[25]
                            Tot_carbon_stems[t]     = Results_MCompound_others1_SC[26]
                            Tot_carbon_roots[t]     = Results_MCompound_others1_SC[27]
                            Tot_co2_stems[t]        = Results_MCompound_others1_SC[28]
                            Tot_co2_roots[t]        = Results_MCompound_others1_SC[29]
                            
                            SC_trees_others_s1_toDelete.remove(str(t))
                                
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                            
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_pine) and (len(SC_trees_others_s1_toDelete) == 0) and (len(SC_trees_spruce_toDelete2) == 0): 
                            Results_LastCompound_pine1_SC = self.LastCompound_pine(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                   Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_pine, 
                                                                                   N_removed, G_before)
                            N_removed               = Results_LastCompound_pine1_SC[0]
                            R_vol_pine              = Results_LastCompound_pine1_SC[1]
                            trees_dict[t]           = Results_LastCompound_pine1_SC[2]
                            volsum[t]               = Results_LastCompound_pine1_SC[3]
                            vol_spruce[t]           = Results_LastCompound_pine1_SC[4]
                            vol_pine[t]             = Results_LastCompound_pine1_SC[5]
                            vol_birch[t]            = Results_LastCompound_pine1_SC[6]
                            vol_others[t]           = Results_LastCompound_pine1_SC[7]
                            vol_ROS[t]              = Results_LastCompound_pine1_SC[8]
                            vol_warm[t]             = Results_LastCompound_pine1_SC[9]
                            R_SPulp[t]              = Results_LastCompound_pine1_SC[10]
                            R_SSaw[t]               = Results_LastCompound_pine1_SC[11]
                            R_HSaw[t]               = Results_LastCompound_pine1_SC[12]
                            R_HPulp[t]              = Results_LastCompound_pine1_SC[13]
                            R_PSaw[t]               = Results_LastCompound_pine1_SC[14]
                            R_PPulp[t]              = Results_LastCompound_pine1_SC[15]
                            G_before                = Results_LastCompound_pine1_SC[16]
                            R_BA                    = Results_LastCompound_pine1_SC[17]
                            ba[t]                   = Results_LastCompound_pine1_SC[18]
                            BGB[t]                  = Results_LastCompound_pine1_SC[19]
                            Tot_co2[t]              = Results_LastCompound_pine1_SC[20]
                            Tot_biomass[t]          = Results_LastCompound_pine1_SC[21]
                            Total_carbon[t]         = Results_LastCompound_pine1_SC[22]
                            Tot_carbon_stems[t]     = Results_LastCompound_pine1_SC[23]
                            Tot_carbon_roots[t]     = Results_LastCompound_pine1_SC[24]
                            Tot_co2_stems[t]        = Results_LastCompound_pine1_SC[25]
                            Tot_co2_roots[t]        = Results_LastCompound_pine1_SC[26]

                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.                                                         

            #mic_t == "High_pine"        
            elif CutFirst == "spruce_others":   
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_spruce) and (len(SC_trees_spruce_toDelete8) !=0):                    
                            Results_1stCompound_spruce7_SC = self.firstCompound_spruce(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, 
                                                                                         Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce,
                                                                                         N_removed, G_before)
                            N_removed                  = Results_1stCompound_spruce7_SC[0]
                            R_vol_spruce               = Results_1stCompound_spruce7_SC[1]
                            trees_dict[t]              = Results_1stCompound_spruce7_SC[2]
                            volsum[t]                  = Results_1stCompound_spruce7_SC[3]
                            vol_spruce[t]              = Results_1stCompound_spruce7_SC[4]
                            vol_pine[t]                = Results_1stCompound_spruce7_SC[5]
                            vol_birch[t]               = Results_1stCompound_spruce7_SC[6]
                            vol_others[t]              = Results_1stCompound_spruce7_SC[7]
                            vol_ROS[t]                 = Results_1stCompound_spruce7_SC[8]
                            vol_warm[t]                = Results_1stCompound_spruce7_SC[9]
                            R_SPulp[t]                 = Results_1stCompound_spruce7_SC[10]
                            R_SSaw[t]                  = Results_1stCompound_spruce7_SC[11]
                            R_HSaw[t]                  = Results_1stCompound_spruce7_SC[12]
                            R_HPulp[t]                 = Results_1stCompound_spruce7_SC[13]
                            R_PSaw[t]                  = Results_1stCompound_spruce7_SC[14]
                            R_PPulp[t]                 = Results_1stCompound_spruce7_SC[15]  
                            G_before                   = Results_1stCompound_spruce7_SC[16]
                            R_BA                       = Results_1stCompound_spruce7_SC[17]
                            ba[t]                      = Results_1stCompound_spruce7_SC[18]
                            BGB[t]                     = Results_1stCompound_spruce7_SC[19]
                            Tot_co2[t]                 = Results_1stCompound_spruce7_SC[20]
                            Tot_biomass[t]             = Results_1stCompound_spruce7_SC[21]
                            Total_carbon[t]            = Results_1stCompound_spruce7_SC[22]
                            Tot_carbon_stems[t]        = Results_1stCompound_spruce7_SC[23]
                            Tot_carbon_roots[t]        = Results_1stCompound_spruce7_SC[24]
                            Tot_co2_stems[t]           = Results_1stCompound_spruce7_SC[25]
                            Tot_co2_roots[t]           = Results_1stCompound_spruce7_SC[26]
                            SC_trees_spruce_toDelete8.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                        
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):
                        if (t in trees_others) and (len(SC_trees_others_s6_toDelete) != 0) and (len(SC_trees_spruce_toDelete8) == 0):       
                            Results_2ndCompound_others5_SC = self.SecondCompound_Others(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, 
                                                                                        Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,R_vol_others,R_vol_ros,R_vol_warm ,
                                                                                        N_removed, G_before)                           
                            
                            N_removed                   = Results_2ndCompound_others5_SC[0]
                            R_vol_birch                 = Results_2ndCompound_others5_SC[1]
                            R_vol_others                = Results_2ndCompound_others5_SC[2]
                            R_vol_ros                   = Results_2ndCompound_others5_SC[3]
                            R_vol_warm                  = Results_2ndCompound_others5_SC[4]
                            trees_dict[t]               = Results_2ndCompound_others5_SC[5]
                            volsum[t]                   = Results_2ndCompound_others5_SC[6]
                            vol_spruce[t]               = Results_2ndCompound_others5_SC[7]
                            vol_pine[t]                 = Results_2ndCompound_others5_SC[8]
                            vol_birch[t]                = Results_2ndCompound_others5_SC[9]
                            vol_others[t]               = Results_2ndCompound_others5_SC[10]
                            vol_ROS[t]                  = Results_2ndCompound_others5_SC[11]
                            vol_warm[t]                 = Results_2ndCompound_others5_SC[12]
                            R_SPulp[t]                  = Results_2ndCompound_others5_SC[13]
                            R_SSaw[t]                   = Results_2ndCompound_others5_SC[14]
                            R_HSaw[t]                   = Results_2ndCompound_others5_SC[15]
                            R_HPulp[t]                  = Results_2ndCompound_others5_SC[16]
                            R_PSaw[t]                   = Results_2ndCompound_others5_SC[17]
                            R_PPulp[t]                  = Results_2ndCompound_others5_SC[18]
                            G_before                    = Results_2ndCompound_others5_SC[19]
                            R_BA                        = Results_2ndCompound_others5_SC[20]
                            ba[t]                       = Results_2ndCompound_others5_SC[21]
                            BGB[t]                      = Results_2ndCompound_others5_SC[22]
                            Tot_co2[t]                  = Results_2ndCompound_others5_SC[23]
                            Tot_biomass[t]              = Results_2ndCompound_others5_SC[24]
                            Total_carbon[t]             = Results_2ndCompound_others5_SC[25]
                            Tot_carbon_stems[t]         = Results_2ndCompound_others5_SC[26]
                            Tot_carbon_roots[t]         = Results_2ndCompound_others5_SC[27]
                            Tot_co2_stems[t]            = Results_2ndCompound_others5_SC[28]
                            Tot_co2_roots[t]            = Results_2ndCompound_others5_SC[29]
                            SC_trees_others_s6_toDelete.remove(str(t))

                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                                                                                            
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and (len(SC_trees_spruce_toDelete8) == 0) and (len(SC_trees_others_s6_toDelete) == 0):  

                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_pine    = R_vol_pine
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.   

            #mic_t == "High_pine"                                         
            elif CutFirst == "others_spruce":
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):          
                        if (t in trees_others) and (len(SC_trees_others_s8_toDelete) != 0):                                     
                            Results_1stCompound_others4_SC = self.firstCompound_others(t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                       Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_birch,
                                                                                       R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before)
                            N_removed                   = Results_1stCompound_others4_SC[0]
                            R_vol_birch                 = Results_1stCompound_others4_SC[1]
                            R_vol_others                = Results_1stCompound_others4_SC[2]
                            R_vol_ros                   = Results_1stCompound_others4_SC[3]
                            R_vol_warm                  = Results_1stCompound_others4_SC[4]
                            trees_dict[t]               = Results_1stCompound_others4_SC[5]
                            volsum[t]                   = Results_1stCompound_others4_SC[6]
                            vol_spruce[t]               = Results_1stCompound_others4_SC[7]
                            vol_pine[t]                 = Results_1stCompound_others4_SC[8]
                            vol_birch[t]                = Results_1stCompound_others4_SC[9]
                            vol_others[t]               = Results_1stCompound_others4_SC[10]
                            vol_ROS[t]                  = Results_1stCompound_others4_SC[11]
                            vol_warm[t]                 = Results_1stCompound_others4_SC[12]
                            R_SPulp[t]                  = Results_1stCompound_others4_SC[13]
                            R_SSaw[t]                   = Results_1stCompound_others4_SC[14]
                            R_HSaw[t]                   = Results_1stCompound_others4_SC[15]
                            R_HPulp[t]                  = Results_1stCompound_others4_SC[16]
                            R_PSaw[t]                   = Results_1stCompound_others4_SC[17]
                            R_PPulp[t]                  = Results_1stCompound_others4_SC[18] 
                            G_before                    = Results_1stCompound_others4_SC[19]
                            R_BA                        = Results_1stCompound_others4_SC[20]
                            ba[t]                       = Results_1stCompound_others4_SC[21]
                            BGB[t]                      = Results_1stCompound_others4_SC[22]
                            Tot_co2[t]                  = Results_1stCompound_others4_SC[23]
                            Tot_biomass[t]              = Results_1stCompound_others4_SC[24]
                            Total_carbon[t]             = Results_1stCompound_others4_SC[25]
                            Tot_carbon_stems[t]         = Results_1stCompound_others4_SC[26]
                            Tot_carbon_roots[t]         = Results_1stCompound_others4_SC[27]
                            Tot_co2_stems[t]            = Results_1stCompound_others4_SC[28]
                            Tot_co2_roots[t]            = Results_1stCompound_others4_SC[29]
                            SC_trees_others_s8_toDelete.remove(str(t))
                            
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                    
                for tree in trees:
                    t = tree
                    if (G_before > BA_left):                                           
                        if (t in trees_spruce) and len(SC_trees_others_s8_toDelete) == 0 and len(SC_trees_spruce_toDelete3) != 0 :                 
                            Results_Compound_Spruce5_only_SC = self.Compound_Spruce_only(t,Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, 
                                                                                         Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots, R_BA, R_vol_spruce ,
                                                                                         N_removed, G_before)
                            N_removed               = Results_Compound_Spruce5_only_SC[0]
                            R_vol_spruce            = Results_Compound_Spruce5_only_SC[1]
                            trees_dict[t]           = Results_Compound_Spruce5_only_SC[2]
                            volsum[t]               = Results_Compound_Spruce5_only_SC[3]
                            vol_spruce[t]           = Results_Compound_Spruce5_only_SC[4]
                            vol_pine[t]             = Results_Compound_Spruce5_only_SC[5]
                            vol_birch[t]            = Results_Compound_Spruce5_only_SC[6]
                            vol_others[t]           = Results_Compound_Spruce5_only_SC[7]
                            vol_ROS[t]              = Results_Compound_Spruce5_only_SC[8]
                            vol_warm[t]             = Results_Compound_Spruce5_only_SC[9]
                            R_SPulp[t]              = Results_Compound_Spruce5_only_SC[10]
                            R_SSaw[t]               = Results_Compound_Spruce5_only_SC[11]
                            R_HSaw[t]               = Results_Compound_Spruce5_only_SC[12]
                            R_HPulp[t]              = Results_Compound_Spruce5_only_SC[13]
                            R_PSaw[t]               = Results_Compound_Spruce5_only_SC[14]
                            R_PPulp[t]              = Results_Compound_Spruce5_only_SC[15]
                            G_before                = Results_Compound_Spruce5_only_SC[16]
                            R_BA                    = Results_Compound_Spruce5_only_SC[17]
                            ba[t]                   = Results_Compound_Spruce5_only_SC[18]
                            BGB[t]                  = Results_Compound_Spruce5_only_SC[19]
                            Tot_co2[t]              = Results_Compound_Spruce5_only_SC[20]
                            Tot_biomass[t]          = Results_Compound_Spruce5_only_SC[21]
                            Total_carbon[t]         = Results_Compound_Spruce5_only_SC[22]
                            Tot_carbon_stems[t]     = Results_Compound_Spruce5_only_SC[23]
                            Tot_carbon_roots[t]     = Results_Compound_Spruce5_only_SC[24]
                            Tot_co2_stems[t]        = Results_Compound_Spruce5_only_SC[25]
                            Tot_co2_roots[t]        = Results_Compound_Spruce5_only_SC[26]
                            SC_trees_spruce_toDelete3.remove(str(t))
                    else:
                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_spruce  = R_vol_spruce
                        R_vol_pine    = R_vol_pine
                        R_vol_birch   = R_vol_birch
                        R_vol_others  = R_vol_others
                        R_vol_ros     = R_vol_ros
                        R_vol_warm    = R_vol_warm
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        
                for tree in trees:
                    t = tree
                    if (t in trees_pine) and (len(SC_trees_others_s8_toDelete) == 0) and (len(SC_trees_spruce_toDelete3) == 0):  

                        n_tree        = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict[t] = n_tree
                        N_removed     = 0
                        R_vol_pine    = R_vol_pine
                        G_before      = G_before
                        R_BA          = R_BA
                        ba[t]         = self.DERIVED_TREES[t].ba
                        BGB[t]              = self.DERIVED_TREES[t].BGB
                        Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                        volsum[t]     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce[t] = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine[t]   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch[t]  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others[t] = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS[t]    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm[t]   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_PSaw[t]     = 0.
                        R_PPulp[t]    = 0.
                        R_HSaw[t]     = 0.
                        R_HPulp[t]    = 0.
                        R_SSaw[t]     = 0.
                        R_SPulp[t]    = 0. 
                                
                                                 
        mgt = mgt     
        for t in trees:
            try:                
                if trees_dict[t] <= .000000001:
                    trees_dict[t] = 0.
            except TypeError:
                ## This part is for the trees which have diameter less than allowance diameterr (check line 10231)
                n_tree              = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict[t]       = n_tree
                ba[t]               = self.DERIVED_TREES[t].ba
                BGB[t]              = self.DERIVED_TREES[t].BGB
                Tot_co2[t]          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass[t]      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon[t]     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems[t] = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots[t] = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems[t]    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots[t]    = self.DERIVED_TREES[t].Tot_co2_roots  
                volsum[t]           = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce[t]       = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine[t]         = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch[t]        = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others[t]       = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS[t]          = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm[t]         = self.tree_volume(t, n_tree, aboveBark= True)[6]
                R_PSaw[t]           = 0.
                R_PPulp[t]          = 0.
                R_HSaw[t]           = 0.
                R_HPulp[t]          = 0.
                R_SSaw[t]           = 0.
                R_SPulp[t]          = 0.

                
            
#            GrowthModel.GROWTH.append((R_SPulp[t], R_SSaw[t]))
            attributes = dict(plot_id = self.DERIVED_TREES[t].plot_id,tree_id = self.DERIVED_TREES[t].tree_id,tree_sp = self.DERIVED_TREES[t].tree_sp, year = year, dbh = self.DERIVED_TREES[t].dbh , 
                              height = self.DERIVED_TREES[t].height, diameter_class = self.DERIVED_TREES[t].diameter_class, tree_Factor =self.DERIVED_TREES[t].tree_Factor , n_tree = trees_dict[t],
                              SI_spp = self.DERIVED_TREES[t].SI_spp, altitude_m = self.DERIVED_TREES[t].altitude_m, SI_m = self.DERIVED_TREES[t].SI_m, LAT = self.DERIVED_TREES[t].LAT, species = self.DERIVED_TREES[t].species, 
                              t_age =self.DERIVED_TREES[t].t_age , Period = period, yr_since_dead = self.DERIVED_TREES[t].yr_since_dead, Num_DeadTrees = self.DERIVED_TREES[t].Num_DeadTrees, Dom_species = self.DERIVED_TREES[t].Dom_species, BGB = BGB[t], Tot_co2 = Tot_co2[t], 
                              Total_carbon = Total_carbon[t],  Tot_carbon_stems = Tot_carbon_stems[t] , Tot_carbon_roots = Tot_carbon_roots[t], Tot_co2_stems = Tot_co2_stems[t], 
                              Tot_co2_roots = Tot_co2_roots[t], Tot_biomass = Tot_biomass[t], vol_increment = self.DERIVED_TREES[t].vol_increment , dead_volume = self.DERIVED_TREES[t].dead_volume,
                              dead_co2 = self.DERIVED_TREES[t].dead_co2, dead_biomass= self.DERIVED_TREES[t].dead_biomass, dead_C = self.DERIVED_TREES[t].dead_C,  R_SPulp = R_SPulp[t], R_PPulp = R_PPulp[t], R_HPulp = R_HPulp[t], 
                              R_SSaw = R_SSaw[t] , R_PSaw =R_PSaw[t], R_HSaw = R_HSaw[t], Biomass_BAR = self.DERIVED_TREES[t].Biomass_BAR, Biomass_LGR = self.DERIVED_TREES[t].Biomass_LGR, Biomass_RGE5 = self.DERIVED_TREES[t].Biomass_RGE5, 
                              Biomass_RLT5= self.DERIVED_TREES[t].Biomass_RLT5, unwl = self.DERIVED_TREES[t].unwl, ufwl = self.DERIVED_TREES[t].ufwl, ucwl = self.DERIVED_TREES[t].ucwl , temp = self.DERIVED_TREES[t].temp, 
                              coord_x = self.DERIVED_TREES[t].coord_x, coord_y = self.DERIVED_TREES[t].coord_y, volsum = volsum[t], vol_spruce = vol_spruce[t], vol_pine = vol_pine[t], vol_birch = vol_birch[t], vol_others = vol_others[t] , 
                              vol_ROS = vol_ROS[t], vol_warm = vol_warm[t], ba = ba[t], management = mgt)
        
            GrowthModel.TreeGenerator(new_cls_name = t , new_parameters= attributes)
        

                                                # %%%%%%  Internal Functions for management part  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    
    def Compound_pine_only(self, t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,
                           R_BA, R_vol_pine ,N_removed, G_before):
        R_PPulp          = 0.
        R_PSaw           = 0.
        R_HSaw           = 0.
        R_HPulp          = 0.
        R_SSaw           = 0.
        R_SPulp          = 0.
        ba               = self.DERIVED_TREES[t].ba
        n_tree           = self.DERIVED_TREES[t].n_tree
        BGB              = self.DERIVED_TREES[t].BGB
        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots
        trees_dict       = n_tree
        volsum           = self.DERIVED_TREES[t].volsum
        vol_spruce       = self.DERIVED_TREES[t].vol_spruce
        vol_pine         = self.DERIVED_TREES[t].vol_pine
        vol_birch        = self.DERIVED_TREES[t].vol_birch
        vol_others       = self.DERIVED_TREES[t].vol_others
        vol_ROS          = self.DERIVED_TREES[t].vol_ROS
        vol_warm         = self.DERIVED_TREES[t].vol_warm
           
        if (R_vol_pine >= self.DERIVED_TREES[t].vol_pine) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
            
            R_PPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[2] * self.tree_volume(t,n_tree, aboveBark= True)[2]
            R_PSaw  = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[3] * self.tree_volume(t,n_tree, aboveBark= True)[2]
            G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            R_vol_pine -= self.tree_volume(t, n_tree, aboveBark= True)[2]
            
            BGB              -= self.DERIVED_TREES[t].BGB
            Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots               
            
            R_BA      -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            ba        -= self.DERIVED_TREES[t].ba
            N_removed -= self.DERIVED_TREES[t].n_tree
            
            n_tree =  0.
            trees_dict = n_tree
            volsum, vol_spruce, vol_pine,vol_birch, vol_others, vol_ROS, vol_warm, R_HSaw, R_HPulp, R_SSaw, R_SPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.
  
        elif (R_vol_pine < self.DERIVED_TREES[t].vol_pine) and (R_BA < (self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree) ):
            removed_rate = N_removed/self.DERIVED_TREES[t].n_tree
            remaining_rate = 1 - removed_rate
            
            removed_rate_pine   = R_vol_pine /self.DERIVED_TREES[t].vol_pine
            remaining_rate_pine = 1 - removed_rate_pine         
            
            if removed_rate_pine != 0. and (self.DERIVED_TREES[t].ba >= 0) :
                N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_pine
                R_PPulp    = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[2] *  self.tree_volume(t,N_removed, aboveBark= True)[2]
                R_PSaw     = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[3] *  self.tree_volume(t,N_removed, aboveBark= True)[2]
                R_vol_pine -= self.tree_volume(t, N_removed, aboveBark= True)[2]
                
                R_BA       -= self.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_pine)
                ba         -= self.DERIVED_TREES[t].ba * removed_rate_pine
                G_before   -= self.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_pine)
                
                n_tree     = self.DERIVED_TREES[t].n_tree * remaining_rate_pine
                trees_dict = n_tree 
                
                BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_pine
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_pine
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_pine
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_pine
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_pine
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_pine
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_pine
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_pine
                
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
              
                R_HSaw,R_HPulp,R_SSaw,R_SPulp    = 0., 0., 0., 0.
  
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict   = n_tree
                N_removed    = 0.
                R_vol_pine   = R_vol_pine
                G_before     = G_before
                R_BA         = R_BA     
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots  
                volsum       = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce   = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine     = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch    = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others   = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS      = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm     = self.tree_volume(t, n_tree, aboveBark= True)[6]                              
                R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.
        else:
            n_tree = self.DERIVED_TREES[t].n_tree * 1.
            trees_dict   = n_tree
            N_removed    = 0.
            R_vol_pine   = R_vol_pine
            G_before     = G_before
            R_BA         = R_BA     
            ba           = self.DERIVED_TREES[t].ba
            BGB              = self.DERIVED_TREES[t].BGB     
            Tot_co2          = self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
            volsum       = self.tree_volume(t, n_tree, aboveBark= True)[0]
            vol_spruce   = self.tree_volume(t, n_tree, aboveBark= True)[1]
            vol_pine     = self.tree_volume(t, n_tree, aboveBark= True)[2]
            vol_birch    = self.tree_volume(t, n_tree, aboveBark= True)[3]
            vol_others   = self.tree_volume(t, n_tree, aboveBark= True)[4]
            vol_ROS      = self.tree_volume(t, n_tree, aboveBark= True)[5]
            vol_warm     = self.tree_volume(t, n_tree, aboveBark= True)[6]                              
            R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.
                

        return N_removed, R_vol_pine, trees_dict, volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SPulp, R_SSaw, R_HSaw, R_HPulp, R_PSaw, R_PPulp, G_before, R_BA, ba, BGB,Tot_co2,Tot_biomass,Total_carbon, Tot_carbon_stems,Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots

                                                # %%%%%% 
    
    def Compound_Spruce_only(self, t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,
                             R_BA, R_vol_spruce ,N_removed, G_before):
        
        R_PPulp          = 0.
        R_PSaw           = 0.
        R_HSaw           = 0.
        R_HPulp          = 0.
        R_SSaw           = 0.
        R_SPulp          = 0.
        ba    = self.DERIVED_TREES[t].ba
        n_tree = self.DERIVED_TREES[t].n_tree
        BGB              = self.DERIVED_TREES[t].BGB
        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots
        trees_dict       = n_tree
        volsum           = self.DERIVED_TREES[t].volsum
        vol_spruce       = self.DERIVED_TREES[t].vol_spruce
        vol_pine         = self.DERIVED_TREES[t].vol_pine
        vol_birch        = self.DERIVED_TREES[t].vol_birch
        vol_others       = self.DERIVED_TREES[t].vol_others
        vol_ROS          = self.DERIVED_TREES[t].vol_ROS
        vol_warm         = self.DERIVED_TREES[t].vol_warm
        
        if (R_vol_spruce >= self.DERIVED_TREES[t].vol_spruce) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
            R_SPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[0] * self.tree_volume(t,n_tree, aboveBark= True)[1]
            R_SSaw  = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[1] * self.tree_volume(t,n_tree, aboveBark= True)[1]
            G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            R_vol_spruce -= self.tree_volume(t, n_tree, aboveBark= True)[1]
            
            BGB              -= self.DERIVED_TREES[t].BGB
            Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
            
            N_removed -= self.DERIVED_TREES[t].n_tree
            R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            ba   -= self.DERIVED_TREES[t].ba
            n_tree =  0.
            trees_dict = n_tree 
            volsum, vol_spruce, vol_pine,vol_birch, vol_others, vol_ROS, vol_warm, R_HSaw, R_HPulp, R_PSaw, R_PPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.
  
        elif (R_vol_spruce < self.DERIVED_TREES[t].vol_spruce) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
            removed_rate = N_removed/self.DERIVED_TREES[t].n_tree
            remaining_rate = 1 - removed_rate                
            removed_rate_spruce   = R_vol_spruce /self.DERIVED_TREES[t].vol_spruce
            remaining_rate_spruce = 1 - removed_rate_spruce         
            
            if removed_rate_spruce != 0. and (self.DERIVED_TREES[t].ba >= 0):
                N_removed = self.DERIVED_TREES[t].n_tree * removed_rate_spruce
                R_SPulp    = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[0] *  self.tree_volume(t,N_removed, aboveBark= True)[1]
                R_SSaw     = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[1] *  self.tree_volume(t,N_removed, aboveBark= True)[1]
                R_vol_spruce -= self.tree_volume(t, N_removed, aboveBark= True)[1]
                
                R_BA       -= self.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_spruce)
                ba         -= self.DERIVED_TREES[t].ba * removed_rate_spruce
                G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_spruce)
                
                n_tree     = self.DERIVED_TREES[t].n_tree * remaining_rate_spruce
                trees_dict = n_tree
                
                BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_spruce
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_spruce
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_spruce
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_spruce
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_spruce
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_spruce
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_spruce
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_spruce
                
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
              
                R_HSaw,R_HPulp,R_PSaw,R_PPulp    = 0., 0., 0., 0.
  
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                N_removed = 0.
                trees_dict   = n_tree
                R_vol_spruce = R_vol_spruce
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum       = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce   = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine     = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch    = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others   = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS      = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm     = self.tree_volume(t, n_tree, aboveBark= True)[6]                              
                R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.
        else:
            n_tree          = self.DERIVED_TREES[t].n_tree * 1.
            N_removed       = 0.
            trees_dict      = n_tree
            R_vol_spruce    = R_vol_spruce
            G_before        = G_before
            R_BA            = R_BA
            ba              = self.DERIVED_TREES[t].ba
            BGB             = self.DERIVED_TREES[t].BGB
            Tot_co2         = self.DERIVED_TREES[t].Tot_co2
            Tot_biomass     = self.DERIVED_TREES[t].Tot_biomass
            Total_carbon    = self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems= self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots= self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems   = self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots   = self.DERIVED_TREES[t].Tot_co2_roots 
            volsum          = self.tree_volume(t, n_tree, aboveBark= True)[0]
            vol_spruce      = self.tree_volume(t, n_tree, aboveBark= True)[1]
            vol_pine        = self.tree_volume(t, n_tree, aboveBark= True)[2]
            vol_birch       = self.tree_volume(t, n_tree, aboveBark= True)[3]
            vol_others      = self.tree_volume(t, n_tree, aboveBark= True)[4]
            vol_ROS         = self.tree_volume(t, n_tree, aboveBark= True)[5]
            vol_warm        = self.tree_volume(t, n_tree, aboveBark= True)[6]                              
            R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.
                
        return N_removed, R_vol_spruce, trees_dict, volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SPulp, R_SSaw, R_HSaw, R_HPulp, R_PSaw, R_PPulp, G_before, R_BA, ba, BGB,Tot_co2,Tot_biomass,Total_carbon, Tot_carbon_stems,Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots

                                                # %%%%%%
                                                
    def firstCompound_others(self,t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,
                             R_BA, R_vol_birch,R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before):
        R_PPulp          = 0.
        R_PSaw           = 0.
        R_HSaw           = 0.
        R_HPulp          = 0.
        R_SSaw           = 0.
        R_SPulp          = 0.
        ba    = self.DERIVED_TREES[t].ba
        n_tree = self.DERIVED_TREES[t].n_tree
        BGB              = self.DERIVED_TREES[t].BGB
        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots
        trees_dict       = n_tree
        volsum           = self.DERIVED_TREES[t].volsum
        vol_spruce       = self.DERIVED_TREES[t].vol_spruce
        vol_pine         = self.DERIVED_TREES[t].vol_pine
        vol_birch        = self.DERIVED_TREES[t].vol_birch
        vol_others       = self.DERIVED_TREES[t].vol_others
        vol_ROS          = self.DERIVED_TREES[t].vol_ROS
        vol_warm         = self.DERIVED_TREES[t].vol_warm
        
        if self.DERIVED_TREES[t].species == "birch":
            if (R_vol_birch >= self.DERIVED_TREES[t].vol_birch) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[3]
                R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh  , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[3]
                R_vol_birch -= self.tree_volume(t, n_tree, aboveBark= True)[3]
                
                BGB              -= self.DERIVED_TREES[t].BGB
                Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                N_removed -= self.DERIVED_TREES[t].n_tree
                R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                ba   -= self.DERIVED_TREES[t].ba
                n_tree =  0.            
                trees_dict = n_tree  
                volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.
            elif (R_vol_birch < self.DERIVED_TREES[t].vol_birch) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                remaining_rate = 1 - removed_rate             
                removed_rate_birch   = R_vol_birch /self.DERIVED_TREES[t].vol_birch
                remaining_rate_birch = 1 - removed_rate_birch 
                
                if removed_rate_birch != 0. and (self.DERIVED_TREES[t].ba >= 0):                                  
                    N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_birch
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[3]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[3]
                    R_vol_birch -= self.tree_volume(t, N_removed, aboveBark= True)[3]
                    
                    R_BA        -= self.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_birch)
                    ba          -= self.DERIVED_TREES[t].ba * removed_rate_birch
                    G_before    -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_birch)
                    
                    n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_birch
                    trees_dict = n_tree
                    
                    BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_birch
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_birch
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_birch
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_birch
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_birch
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_birch
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_birch
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_birch
                    
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                    
                    R_SSaw, R_SPulp, R_PSaw,R_PPulp  = 0., 0., 0., 0.

                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree
                    N_removed = 0.
                    R_vol_birch= R_vol_birch
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp,R_SSaw,R_SPulp,R_PSaw,R_PPulp = 0., 0.,0.,0.,0.,0.
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict = n_tree
                N_removed = 0.
                R_vol_birch= R_vol_birch
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                R_HSaw, R_HPulp,R_SSaw,R_SPulp,R_PSaw,R_PPulp = 0., 0.,0.,0.,0.,0.
               
        elif self.DERIVED_TREES[t].species == "other_broadleaves":
            if (R_vol_others >= self.DERIVED_TREES[t].vol_others) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[4]
                R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[4]
                R_vol_others -= self.tree_volume(t, n_tree, aboveBark= True)[4]
                
                BGB              -= self.DERIVED_TREES[t].BGB
                Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                
                G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                N_removed -= self.DERIVED_TREES[t].n_tree
                R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                ba   -= self.DERIVED_TREES[t].ba
                n_tree =  0.            
                trees_dict = n_tree  
                volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.
            
            elif (R_vol_others < self.DERIVED_TREES[t].vol_others) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                remaining_rate = 1 - removed_rate               
                removed_rate_others   = R_vol_others/self.DERIVED_TREES[t].vol_others
                remaining_rate_others = 1 - removed_rate_others
                
                if removed_rate_others != 0. and (self.DERIVED_TREES[t].ba >= 0):
                    N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_others
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[4]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[4]
                    R_vol_others -= self.tree_volume(t, N_removed, aboveBark= True)[4]
                    
                    R_BA       -= self.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_others)
                    ba         -= self.DERIVED_TREES[t].ba * removed_rate_others
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_others)
                                       
                    n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_others
                    trees_dict = n_tree
                    
                    BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_others
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_others
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_others
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_others
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_others
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_others
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_others
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_others
                    
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                    
                    R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0.

                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict  = n_tree
                    N_removed = 0.
                    R_vol_others= R_vol_others
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum      = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce  = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine    = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch   = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others  = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS     = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm    = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp    = 0., 0., 0., 0., 0., 0.
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict  = n_tree
                N_removed = 0.
                R_vol_others= R_vol_others
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum      = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce  = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine    = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch   = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others  = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS     = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm    = self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp    = 0., 0., 0., 0., 0., 0.
        
        elif self.DERIVED_TREES[t].species == "ROS":
            if (R_vol_ros >= self.DERIVED_TREES[t].vol_ROS) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree):
                R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[5]
                R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[5]
                R_vol_ros -= self.tree_volume(t, n_tree, aboveBark= True)[5]
                
                BGB              -= self.DERIVED_TREES[t].BGB
                Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                
                G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                N_removed -= self.DERIVED_TREES[t].n_tree
                R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                ba   -= self.DERIVED_TREES[t].ba
                n_tree =  0.            
                trees_dict = n_tree  
                volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0. 
            
            elif (R_vol_ros < self.DERIVED_TREES[t].vol_ROS) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                remaining_rate = 1 - removed_rate
                removed_rate_ros   = R_vol_ros/self.DERIVED_TREES[t].vol_ROS
                remaining_rate_ros = 1 - removed_rate_ros
                
                if removed_rate_ros != 0. and (self.DERIVED_TREES[t].ba >= 0):
                    N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_ros
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[5]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[5]
                    R_vol_ros -= self.tree_volume(t, N_removed, aboveBark= True)[5]
                    
                    R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_ros
                    ba         -= self.DERIVED_TREES[t].ba * removed_rate_ros
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_ros)
                    
                    n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_ros
                    trees_dict = n_tree
                    
                    BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_ros
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_ros
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_ros
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_ros
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_ros
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_ros
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_ros
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_ros
                    
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                    
                    R_SSaw, R_SPulp, R_PSaw,R_PPulp  = 0., 0., 0., 0.

                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree 
                    N_removed = 0.
                    R_vol_ros  = R_vol_ros
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp   = 0., 0., 0., 0., 0., 0.
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict = n_tree 
                N_removed = 0.
                R_vol_ros  = R_vol_ros
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp   = 0., 0., 0., 0., 0., 0.
        
        elif self.DERIVED_TREES[t].species == "warm":
            if (R_vol_warm >= self.DERIVED_TREES[t].vol_warm) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[6]
                R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[6]
                R_vol_warm -= self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                BGB              -= self.DERIVED_TREES[t].BGB
                Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                
                G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                N_removed -= self.DERIVED_TREES[t].n_tree
                R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                ba   -= self.DERIVED_TREES[t].ba
                n_tree =  0.            
                trees_dict = n_tree  
                volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0. 
            
            elif (R_vol_warm < self.DERIVED_TREES[t].vol_warm) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                remaining_rate = 1 - removed_rate
                removed_rate_warm   = R_vol_warm/self.DERIVED_TREES[t].vol_warm
                remaining_rate_warm = 1 - removed_rate_warm
                
                if removed_rate_warm != 0. and (self.DERIVED_TREES[t].ba >= 0):
                    N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_warm
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[6]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[6]
                    R_vol_warm -= self.tree_volume(t, N_removed, aboveBark= True)[6]
                    
                    R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_warm
                    ba         -= self.DERIVED_TREES[t].ba * removed_rate_warm
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_warm)
                    
                    n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_warm
                    trees_dict = n_tree
                    
                    BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_warm
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_warm
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_warm
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_warm
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_warm
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_warm
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_warm
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_warm
                    
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                    
                    R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0.

                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree 
                    N_removed = 0.
                    R_vol_warm = R_vol_warm
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0. 
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict = n_tree 
                N_removed = 0.
                R_vol_warm = R_vol_warm
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.
        
        
        return N_removed, R_vol_birch, R_vol_others, R_vol_ros, R_vol_warm, trees_dict, volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SPulp, R_SSaw, R_HSaw, R_HPulp, R_PSaw, R_PPulp, G_before , R_BA, ba, BGB,Tot_co2,Tot_biomass,Total_carbon, Tot_carbon_stems,Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots   

                                                # %%%%%%
                                                
    def firstCompound_pine(self,t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,
                           R_BA, R_vol_pine,N_removed, G_before):
        R_PPulp          = 0.
        R_PSaw           = 0.
        R_HSaw           = 0.
        R_HPulp          = 0.
        R_SSaw           = 0.
        R_SPulp          = 0.
        ba    = self.DERIVED_TREES[t].ba
        n_tree = self.DERIVED_TREES[t].n_tree
        BGB              = self.DERIVED_TREES[t].BGB
        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots
        trees_dict       = n_tree
        volsum           = self.DERIVED_TREES[t].volsum
        vol_spruce       = self.DERIVED_TREES[t].vol_spruce
        vol_pine         = self.DERIVED_TREES[t].vol_pine
        vol_birch        = self.DERIVED_TREES[t].vol_birch
        vol_others       = self.DERIVED_TREES[t].vol_others
        vol_ROS          = self.DERIVED_TREES[t].vol_ROS
        vol_warm         = self.DERIVED_TREES[t].vol_warm
        
        if (R_vol_pine >= self.DERIVED_TREES[t].vol_pine) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
            R_PPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[2] * self.tree_volume(t,n_tree, aboveBark= True)[2]
            R_PSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[3] * self.tree_volume(t,n_tree, aboveBark= True)[2]
            R_vol_pine -= self.tree_volume(t, n_tree, aboveBark= True)[2]
            
            BGB              -= self.DERIVED_TREES[t].BGB
            Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
            
            G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            N_removed -= self.DERIVED_TREES[t].n_tree
            R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            ba   -= self.DERIVED_TREES[t].ba
            n_tree =  0.
            trees_dict = n_tree                            
            volsum, vol_spruce, vol_pine,vol_birch, vol_others, vol_ROS, vol_warm, R_HSaw, R_HPulp, R_SSaw, R_SPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.
        elif (R_vol_pine < self.DERIVED_TREES[t].vol_pine) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
            removed_rate = N_removed/self.DERIVED_TREES[t].n_tree
            remaining_rate = 1 - removed_rate
            removed_rate_pine   = R_vol_pine /self.DERIVED_TREES[t].vol_pine
            remaining_rate_pine = 1 - removed_rate_pine         
            
            if removed_rate_pine != 0. and (self.DERIVED_TREES[t].ba >= 0):        
                N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_pine
                R_PPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[2] * self.tree_volume(t,N_removed, aboveBark= True)[2]
                R_PSaw  = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[3] * self.tree_volume(t,N_removed, aboveBark= True)[2]
                R_vol_pine -= self.tree_volume(t, N_removed, aboveBark= True)[2]
                
                R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_pine
                ba         -= self.DERIVED_TREES[t].ba * removed_rate_pine
                G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_pine)
                
                n_tree     = self.DERIVED_TREES[t].n_tree * remaining_rate_pine
                trees_dict = n_tree
                
                BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_pine
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_pine
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_pine
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_pine
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_pine
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_pine
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_pine
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_pine
                
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
              
                R_HSaw,R_HPulp,R_SSaw,R_SPulp    = 0., 0., 0., 0.
                 
            else:
                n_tree     = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict = n_tree
                N_removed = 0.
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                                                              
                R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.

        else:
            n_tree     = self.DERIVED_TREES[t].n_tree * 1.
            trees_dict = n_tree
            N_removed = 0.
            G_before     = G_before
            R_BA         = R_BA
            ba           = self.DERIVED_TREES[t].ba
            BGB              = self.DERIVED_TREES[t].BGB
            Tot_co2          = self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
            volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
            vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
            vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
            vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
            vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
            vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
            vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                                                              
            R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0. 
        
        return N_removed, R_vol_pine, trees_dict, volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SPulp, R_SSaw, R_HSaw, R_HPulp, R_PSaw, R_PPulp, G_before, R_BA, ba, BGB,Tot_co2,Tot_biomass,Total_carbon, Tot_carbon_stems,Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots   
                   
                                                # %%%%%%
                                                
    def firstCompound_spruce(self,t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,
                             R_BA, R_vol_spruce,N_removed, G_before):
        R_PPulp          = 0.
        R_PSaw           = 0.
        R_HSaw           = 0.
        R_HPulp          = 0.
        R_SSaw           = 0.
        R_SPulp          = 0.
        ba    = self.DERIVED_TREES[t].ba  
        n_tree = self.DERIVED_TREES[t].n_tree
        BGB              = self.DERIVED_TREES[t].BGB
        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots
        trees_dict       = n_tree
        volsum           = self.DERIVED_TREES[t].volsum
        vol_spruce       = self.DERIVED_TREES[t].vol_spruce
        vol_pine         = self.DERIVED_TREES[t].vol_pine
        vol_birch        = self.DERIVED_TREES[t].vol_birch
        vol_others       = self.DERIVED_TREES[t].vol_others
        vol_ROS          = self.DERIVED_TREES[t].vol_ROS
        vol_warm         = self.DERIVED_TREES[t].vol_warm
        
        if (R_vol_spruce >= self.DERIVED_TREES[t].vol_spruce) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
            R_SPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[0] * self.tree_volume(t, n_tree, aboveBark= True)[1]
            R_SSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[1] * self.tree_volume(t,n_tree, aboveBark= True)[1]
            R_vol_spruce -= self.tree_volume(t, n_tree, aboveBark= True)[1]
            
            BGB              -= self.DERIVED_TREES[t].BGB
            Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
            
            G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            N_removed -= self.DERIVED_TREES[t].n_tree        
            R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            ba   -= self.DERIVED_TREES[t].ba
            n_tree =  0.
            trees_dict = n_tree                            
            volsum, vol_spruce, vol_pine,vol_birch, vol_others, vol_ROS, vol_warm, R_HSaw, R_HPulp, R_PSaw, R_PPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.

        elif (R_vol_spruce < self.DERIVED_TREES[t].vol_spruce) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
            removed_rate = N_removed/self.DERIVED_TREES[t].n_tree
            remaining_rate = 1 - removed_rate               
            removed_rate_spruce   = R_vol_spruce /self.DERIVED_TREES[t].vol_spruce
            remaining_rate_spruce = 1 - removed_rate_spruce         
            
            if removed_rate_spruce != 0. and (self.DERIVED_TREES[t].ba >= 0):
                N_removed = self.DERIVED_TREES[t].n_tree * removed_rate_spruce
                R_SPulp    = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[0] *  self.tree_volume(t,N_removed, aboveBark= True)[1]
                R_SSaw     = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[1] *  self.tree_volume(t,N_removed, aboveBark= True)[1]
                R_vol_spruce -= self.tree_volume(t, N_removed, aboveBark= True)[1]
                
                R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_spruce
                ba         -= self.DERIVED_TREES[t].ba * removed_rate_spruce
                G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_spruce)
                
                n_tree     = self.DERIVED_TREES[t].n_tree * remaining_rate_spruce
                trees_dict = n_tree 
                
                BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_spruce
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_spruce
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_spruce
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_spruce
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_spruce
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_spruce
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_spruce
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_spruce
                
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
              
                R_HSaw,R_HPulp,R_PSaw,R_PPulp    = 0., 0., 0., 0.
  
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                N_removed = 0.
                trees_dict   = n_tree
                R_vol_spruce = R_vol_spruce
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum       = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce   = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine     = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch    = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others   = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS      = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm     = self.tree_volume(t, n_tree, aboveBark= True)[6]                              
                R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.
        else:
            n_tree = self.DERIVED_TREES[t].n_tree * 1.
            N_removed = 0.
            trees_dict   = n_tree
            R_vol_spruce = R_vol_spruce
            G_before     = G_before
            R_BA         = R_BA
            ba           = self.DERIVED_TREES[t].ba
            BGB              = self.DERIVED_TREES[t].BGB
            Tot_co2          = self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
            volsum       = self.tree_volume(t, n_tree, aboveBark= True)[0]
            vol_spruce   = self.tree_volume(t, n_tree, aboveBark= True)[1]
            vol_pine     = self.tree_volume(t, n_tree, aboveBark= True)[2]
            vol_birch    = self.tree_volume(t, n_tree, aboveBark= True)[3]
            vol_others   = self.tree_volume(t, n_tree, aboveBark= True)[4]
            vol_ROS      = self.tree_volume(t, n_tree, aboveBark= True)[5]
            vol_warm     = self.tree_volume(t, n_tree, aboveBark= True)[6]                              
            R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.
            
        return N_removed, R_vol_spruce, trees_dict, volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SPulp, R_SSaw, R_HSaw, R_HPulp, R_PSaw, R_PPulp, G_before, R_BA, ba, BGB,Tot_co2,Tot_biomass,Total_carbon, Tot_carbon_stems,Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots

                                                # %%%%%%
                                                
    def MiddleCompound_Others(self,t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,
                              R_BA, R_vol_birch,R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before):
            R_PPulp          = 0.
            R_PSaw           = 0.
            R_HSaw           = 0.
            R_HPulp          = 0.
            R_SSaw           = 0.
            R_SPulp          = 0.
            n_tree = self.DERIVED_TREES[t].n_tree
            ba    = self.DERIVED_TREES[t].ba
            BGB              = self.DERIVED_TREES[t].BGB
            Tot_co2          = self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots
            trees_dict       = n_tree
            volsum           = self.DERIVED_TREES[t].volsum
            vol_spruce       = self.DERIVED_TREES[t].vol_spruce
            vol_pine         = self.DERIVED_TREES[t].vol_pine
            vol_birch        = self.DERIVED_TREES[t].vol_birch
            vol_others       = self.DERIVED_TREES[t].vol_others
            vol_ROS          = self.DERIVED_TREES[t].vol_ROS
            vol_warm         = self.DERIVED_TREES[t].vol_warm
            
            if self.DERIVED_TREES[t].species == "birch":
                if (R_vol_birch >= self.DERIVED_TREES[t].vol_birch) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[3]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[3]
                    R_vol_birch -= self.tree_volume(t, n_tree, aboveBark= True)[3]
                    
                    BGB              -= self.DERIVED_TREES[t].BGB
                    Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                    
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                    N_removed -= self.DERIVED_TREES[t].n_tree
                    R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                    ba   -= self.DERIVED_TREES[t].ba
                    n_tree =  0.        
                    trees_dict = n_tree
                    volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw,R_SPulp, R_PSaw, R_PPulp = 0., 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.
                elif (R_vol_birch < self.DERIVED_TREES[t].vol_birch) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                    removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                    remaining_rate = 1 - removed_rate
                    removed_rate_birch   = R_vol_birch /self.DERIVED_TREES[t].vol_birch
                    remaining_rate_birch = 1 - removed_rate_birch 
                    
                    if removed_rate_birch != 0. and (self.DERIVED_TREES[t].ba >= 0):                                  
                        N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_birch
                        R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[3]
                        R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[3]
                        R_vol_birch -= self.tree_volume(t, N_removed, aboveBark= True)[3]
                        
                        R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_birch
                        ba         -= self.DERIVED_TREES[t].ba * removed_rate_birch
                        G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_birch)
                        
                        n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_birch
                        trees_dict = n_tree
                        
                        BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_birch
                        Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_birch
                        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_birch
                        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_birch
                        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_birch
                        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_birch
                        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_birch
                        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_birch
                        
                        volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                        
                        R_SSaw, R_SPulp, R_PSaw,R_PPulp  = 0., 0., 0., 0.

                    else:
                        n_tree = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict = n_tree 
                        N_removed  = 0.
                        R_vol_birch= R_vol_birch
                        G_before   = G_before
                        R_BA       = R_BA
                        ba         = self.DERIVED_TREES[t].ba
                        BGB              = self.DERIVED_TREES[t].BGB
                        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.
                        
                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree 
                    N_removed  = 0.
                    R_vol_birch= R_vol_birch
                    G_before   = G_before
                    R_BA       = R_BA
                    ba         = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.
                            
            elif self.DERIVED_TREES[t].species == "other_broadleaves":
                if (R_vol_others >= self.DERIVED_TREES[t].vol_others) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[4]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[4]
                    R_vol_others -= self.tree_volume(t, n_tree, aboveBark= True)[4]
                    
                    BGB              -= self.DERIVED_TREES[t].BGB
                    Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                    
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                    N_removed -= self.DERIVED_TREES[t].n_tree
                    R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree                   
                    ba   -= self.DERIVED_TREES[t].ba
                    n_tree =  0.
                    trees_dict = n_tree
                    volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp = 0., 0.,0.,0.,0.,0.,0., 0.,0.,0.,0.
                
                elif (R_vol_others < self.DERIVED_TREES[t].vol_others) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                    removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                    remaining_rate = 1 - removed_rate
                    removed_rate_others   = R_vol_others/self.DERIVED_TREES[t].vol_others
                    remaining_rate_others = 1 - removed_rate_others
                    
                    if removed_rate_others != 0. and (self.DERIVED_TREES[t].ba >= 0):
                        N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_others
                        R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[4]
                        R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[4]
                        R_vol_others -= self.tree_volume(t, N_removed, aboveBark= True)[4]
                        
                        R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_others
                        ba         -= self.DERIVED_TREES[t].ba * removed_rate_others
                        G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_others)
                        
                        n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_others
                        trees_dict = n_tree
                        
                        BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_others
                        Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_others
                        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_others
                        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_others
                        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_others
                        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_others
                        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_others
                        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_others
                        
                        volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                        
                        R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0.

                    else:
                        n_tree = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict  = n_tree 
                        N_removed   = 0.
                        R_vol_others= R_vol_others
                        G_before    = G_before
                        R_BA        = R_BA
                        ba          = self.DERIVED_TREES[t].ba
                        BGB              = self.DERIVED_TREES[t].BGB
                        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum      = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce  = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine    = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch   = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others  = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS     = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm    = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.
                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict  = n_tree 
                    N_removed   = 0.
                    R_vol_others= R_vol_others
                    G_before    = G_before
                    R_BA        = R_BA
                    ba          = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum      = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce  = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine    = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch   = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others  = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS     = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm    = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.
                    
            elif self.DERIVED_TREES[t].species == "ROS":
                if (R_vol_ros >= self.DERIVED_TREES[t].vol_ROS) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[5]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[5]
                    R_vol_ros -= self.tree_volume(t, n_tree, aboveBark= True)[5]
                    
                    BGB              -= self.DERIVED_TREES[t].BGB
                    Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                    
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                    N_removed -= self.DERIVED_TREES[t].n_tree
                    R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                    ba   -= self.DERIVED_TREES[t].ba
                    n_tree =  0.
                    trees_dict = n_tree
                    volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.
                elif (R_vol_ros < self.DERIVED_TREES[t].vol_ROS) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                    removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                    remaining_rate = 1 - removed_rate
                    removed_rate_ros   = R_vol_ros/self.DERIVED_TREES[t].vol_ROS
                    remaining_rate_ros = 1 - removed_rate_ros
                    
                    if removed_rate_ros != 0. and (self.DERIVED_TREES[t].ba >= 0):
                        N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_ros
                        R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[5]
                        R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[5]
                        R_vol_ros -= self.tree_volume(t, N_removed, aboveBark= True)[5]
                        
                        R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_ros
                        ba         -= self.DERIVED_TREES[t].ba * removed_rate_ros
                        G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_ros)
                        
                        n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_ros
                        trees_dict = n_tree
                        
                        BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_ros
                        Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_ros
                        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_ros
                        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_ros
                        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_ros
                        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_ros
                        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_ros
                        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_ros
                        
                        volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                        
                        R_SSaw, R_SPulp, R_PSaw,R_PPulp  = 0., 0., 0., 0.
    
                    else:
                        n_tree = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict = n_tree
                        N_removed = 0.
                        R_vol_ros  = R_vol_ros
                        G_before     = G_before
                        R_BA         = R_BA
                        ba           = self.DERIVED_TREES[t].ba
                        BGB              = self.DERIVED_TREES[t].BGB
                        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        
                        R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.
                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree
                    N_removed = 0.
                    R_vol_ros  = R_vol_ros
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]  
                    
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.
                    
            elif self.DERIVED_TREES[t].species == "warm":
                if (R_vol_warm >= self.DERIVED_TREES[t].vol_warm) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[6]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[6]
                    R_vol_warm -= self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    BGB              -= self.DERIVED_TREES[t].BGB
                    Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                    
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                    N_removed -= self.DERIVED_TREES[t].n_tree
                    R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                    ba   -= self.DERIVED_TREES[t].ba
                    n_tree =  0.
                    trees_dict = n_tree
                    volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0., 0., 0., 0., 0., 0.
                elif (R_vol_warm < self.DERIVED_TREES[t].vol_warm) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                    removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                    remaining_rate = 1 - removed_rate
                    removed_rate_warm   = R_vol_warm/self.DERIVED_TREES[t].vol_warm
                    remaining_rate_warm = 1 - removed_rate_warm
                    
                    if removed_rate_warm != 0. and (self.DERIVED_TREES[t].ba >= 0):
                        N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_warm
                        R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[6]
                        R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[6]
                        R_vol_warm -= self.tree_volume(t, N_removed, aboveBark= True)[6]
                        
                        R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_warm
                        ba         -= self.DERIVED_TREES[t].ba * removed_rate_warm
                        G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_warm)
                        
                        n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_warm
                        trees_dict = n_tree
                        
                        BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_warm
                        Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_warm
                        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_warm
                        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_warm
                        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_warm
                        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_warm
                        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_warm
                        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_warm
                        
                        volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                        
                        R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0.
    
                    else:
                        n_tree = self.DERIVED_TREES[t].n_tree * 1.
                        trees_dict = n_tree 
                        N_removed = 0.
                        R_vol_warm = R_vol_warm
                        G_before     = G_before
                        R_BA         = R_BA
                        ba           = self.DERIVED_TREES[t].ba
                        BGB              = self.DERIVED_TREES[t].BGB
                        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                        volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                        vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                        vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                        vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                        vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                        vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                        vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                        
                        R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.
                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree 
                    N_removed = 0.
                    R_vol_warm = R_vol_warm
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.                       
                    
            return N_removed, R_vol_birch, R_vol_others, R_vol_ros, R_vol_warm, trees_dict, volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SPulp, R_SSaw, R_HSaw, R_HPulp, R_PSaw, R_PPulp, G_before, R_BA, ba, BGB,Tot_co2,Tot_biomass,Total_carbon, Tot_carbon_stems,Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots

                                                # %%%%%%
                                                
    def LastCompound_pine(self, t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,
                          R_BA, R_vol_pine, N_removed, G_before):
        R_PPulp          = 0.
        R_PSaw           = 0.
        R_HSaw           = 0.
        R_HPulp          = 0.
        R_SSaw           = 0.
        R_SPulp          = 0.
        ba    = self.DERIVED_TREES[t].ba
        n_tree = self.DERIVED_TREES[t].n_tree
        BGB              = self.DERIVED_TREES[t].BGB
        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots
        trees_dict       = n_tree
        volsum           = self.DERIVED_TREES[t].volsum
        vol_spruce       = self.DERIVED_TREES[t].vol_spruce
        vol_pine         = self.DERIVED_TREES[t].vol_pine
        vol_birch        = self.DERIVED_TREES[t].vol_birch
        vol_others       = self.DERIVED_TREES[t].vol_others
        vol_ROS          = self.DERIVED_TREES[t].vol_ROS
        vol_warm         = self.DERIVED_TREES[t].vol_warm
        
        if (R_vol_pine >= GrowthModel.DERIVED_TREES[t].vol_pine) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):        
            R_PPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[2] * self.tree_volume(t,n_tree, aboveBark= True)[2]
            R_PSaw  = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[3] * self.tree_volume(t,n_tree, aboveBark= True)[2]
            R_vol_pine -= self.tree_volume(t, n_tree, aboveBark= True)[2]
            
            BGB              -= self.DERIVED_TREES[t].BGB
            Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
            
            G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            N_removed -= self.DERIVED_TREES[t].n_tree
            R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
            ba   -= self.DERIVED_TREES[t].ba
            n_tree =  0.
            trees_dict = n_tree
            volsum, vol_spruce, vol_pine,vol_birch, vol_others, vol_ROS, vol_warm, R_HSaw, R_HPulp, R_SSaw, R_SPulp  = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.
        
        elif (R_vol_pine < self.DERIVED_TREES[t].vol_pine) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
            removed_rate = N_removed/self.DERIVED_TREES[t].n_tree
            remaining_rate = 1 - removed_rate
            removed_rate_pine   = R_vol_pine /self.DERIVED_TREES[t].vol_pine
            remaining_rate_pine = 1 - removed_rate_pine         
            
            if removed_rate_pine != 0. and (self.DERIVED_TREES[t].ba >= 0):        
                N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_pine
                R_PPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[2] * self.tree_volume(t,N_removed, aboveBark= True)[2]
                R_PSaw  = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[3] * self.tree_volume(t,N_removed, aboveBark= True)[2]
                R_vol_pine -= self.tree_volume(t, N_removed, aboveBark= True)[2]
                
                R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_pine
                ba         -= self.DERIVED_TREES[t].ba * removed_rate_pine
                G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_pine)
                
                n_tree     = self.DERIVED_TREES[t].n_tree * remaining_rate_pine
                trees_dict = n_tree 
                
                BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_pine
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_pine
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_pine
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_pine
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_pine
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_pine
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_pine
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_pine
                
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
              
                R_HSaw,R_HPulp,R_SSaw,R_SPulp    = 0., 0., 0., 0.
                 
            else:
                n_tree     = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict = n_tree
                N_removed = 0.
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                                                              
                R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.

        else:
            n_tree     = self.DERIVED_TREES[t].n_tree * 1.
            trees_dict = n_tree
            N_removed = 0.
            G_before     = G_before
            R_BA         = R_BA
            ba           = self.DERIVED_TREES[t].ba
            BGB              = self.DERIVED_TREES[t].BGB
            Tot_co2          = self.DERIVED_TREES[t].Tot_co2
            Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
            Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
            Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
            Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
            Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
            Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
            volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
            vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
            vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
            vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
            vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
            vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
            vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                                                              
            R_SSaw, R_SPulp, R_HSaw, R_HPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0.               
        
        return N_removed, R_vol_pine, trees_dict, volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SPulp, R_SSaw, R_HSaw, R_HPulp, R_PSaw, R_PPulp, G_before, R_BA, ba, BGB,Tot_co2,Tot_biomass,Total_carbon, Tot_carbon_stems,Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots

                                                # %%%%%%
                                                
    def SecondCompound_Others(self,t, Remove_BGB, Remove_co2, Remove_biomass, Remove_carbon, Remove_carbon_stems, Remove_carbon_roots, Remove_co2_stems, Remove_co2_roots,
                              R_BA, R_vol_birch,R_vol_others,R_vol_ros,R_vol_warm ,N_removed, G_before):
        R_PPulp          = 0.
        R_PSaw           = 0.
        R_HSaw           = 0.
        R_HPulp          = 0.
        R_SSaw           = 0.
        R_SPulp          = 0.
        n_tree = self.DERIVED_TREES[t].n_tree
        ba    = self.DERIVED_TREES[t].ba
        BGB              = self.DERIVED_TREES[t].BGB
        Tot_co2          = self.DERIVED_TREES[t].Tot_co2
        Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
        Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
        Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
        Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
        Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
        Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots
        trees_dict       = n_tree
        volsum           = self.DERIVED_TREES[t].volsum
        vol_spruce       = self.DERIVED_TREES[t].vol_spruce
        vol_pine         = self.DERIVED_TREES[t].vol_pine
        vol_birch        = self.DERIVED_TREES[t].vol_birch
        vol_others       = self.DERIVED_TREES[t].vol_others
        vol_ROS          = self.DERIVED_TREES[t].vol_ROS
        vol_warm         = self.DERIVED_TREES[t].vol_warm
        
        if self.DERIVED_TREES[t].species == "birch":
            if (R_vol_birch >= self.DERIVED_TREES[t].vol_birch) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[3]
                R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[3]
                R_vol_birch -= self.tree_volume(t, n_tree, aboveBark= True)[3]
                
                BGB              -= self.DERIVED_TREES[t].BGB
                Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                
                G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                N_removed -= self.DERIVED_TREES[t].n_tree
                R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                ba   -= self.DERIVED_TREES[t].ba
                n_tree =  0.
                trees_dict = n_tree
                volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw,R_SPulp, R_PSaw, R_PPulp = 0., 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.

            elif (R_vol_birch < self.DERIVED_TREES[t].vol_birch) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                remaining_rate = 1 - removed_rate
                removed_rate_birch   = R_vol_birch /self.DERIVED_TREES[t].vol_birch
                remaining_rate_birch = 1 - removed_rate_birch 
                
                if removed_rate_birch != 0.  and (self.DERIVED_TREES[t].ba >= 0):                                  
                    N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_birch
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[3]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[3]
                    R_vol_birch -= self.tree_volume(t, N_removed, aboveBark= True)[3]
                    
                    R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_birch
                    ba         -= self.DERIVED_TREES[t].ba * removed_rate_birch
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_birch)
                    
                    n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_birch
                    trees_dict = n_tree
                    
                    BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_birch
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_birch
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_birch
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_birch
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_birch
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_birch
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_birch
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_birch
                    
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                    
                    R_SSaw, R_SPulp, R_PSaw,R_PPulp  = 0., 0., 0., 0.

                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree 
                    N_removed = 0.
                    R_vol_birch= R_vol_birch
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp,R_SSaw,R_SPulp,R_PSaw,R_PPulp = 0., 0.,0.,0.,0.,0.

            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict = n_tree 
                N_removed = 0.
                R_vol_birch= R_vol_birch
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                R_HSaw, R_HPulp,R_SSaw,R_SPulp,R_PSaw,R_PPulp = 0., 0.,0.,0.,0.,0.                                                   
                
        elif self.DERIVED_TREES[t].species == "other_broadleaves": 
            if (R_vol_others >= self.DERIVED_TREES[t].vol_others) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[4]
                R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[4]
                R_vol_others -= self.tree_volume(t, n_tree, aboveBark= True)[4]
                
                BGB              -= self.DERIVED_TREES[t].BGB
                Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                
                G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                N_removed -= self.DERIVED_TREES[t].n_tree
                R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                ba   -= self.DERIVED_TREES[t].ba
                n_tree =  0.
                trees_dict = n_tree
                volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp = 0., 0.,0.,0.,0.,0.,0., 0.,0.,0.,0.

            elif (R_vol_others < self.DERIVED_TREES[t].vol_others) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                remaining_rate = 1 - removed_rate
                removed_rate_others   = R_vol_others/self.DERIVED_TREES[t].vol_others
                remaining_rate_others = 1 - removed_rate_others
                
                if removed_rate_others != 0. and (self.DERIVED_TREES[t].ba >= 0):
                    N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_others
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[4]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[4]
                    R_vol_others -= self.tree_volume(t, N_removed, aboveBark= True)[4]
                    
                    R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_others
                    ba         -= self.DERIVED_TREES[t].ba * removed_rate_others
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_others)
                    
                    n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_others
                    trees_dict = n_tree
                    
                    BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_others
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_others
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_others
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_others
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_others
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_others
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_others
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_others
                    
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                    
                    R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0.

                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict  = n_tree
                    N_removed = 0.
                    R_vol_others= R_vol_others
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum      = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce  = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine    = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch   = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others  = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS     = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm    = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp    = 0., 0., 0., 0., 0., 0.
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict  = n_tree
                N_removed = 0.
                R_vol_others= R_vol_others
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum      = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce  = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine    = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch   = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others  = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS     = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm    = self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp    = 0., 0., 0., 0., 0., 0.
                
        elif self.DERIVED_TREES[t].species == "ROS": 
            if (R_vol_ros >= self.DERIVED_TREES[t].vol_ROS) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[5]
                R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[5]
                R_vol_ros -= self.tree_volume(t, n_tree, aboveBark= True)[5]
                
                BGB              -= self.DERIVED_TREES[t].BGB
                Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                
                G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                N_removed -= self.DERIVED_TREES[t].n_tree
                R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                ba   -= self.DERIVED_TREES[t].ba
                n_tree =  0.
                trees_dict = n_tree
                volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp = 0.,0.,0.,0.,0.,0.,0.,0.,0.,0.,0.

            elif (R_vol_ros < self.DERIVED_TREES[t].vol_ROS) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                remaining_rate = 1 - removed_rate
                removed_rate_ros   = R_vol_ros/self.DERIVED_TREES[t].vol_ROS
                remaining_rate_ros = 1 - removed_rate_ros
                
                if removed_rate_ros != 0. and (self.DERIVED_TREES[t].ba >= 0):
                    N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_ros
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[5]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[5]
                    R_vol_ros -= self.tree_volume(t, N_removed, aboveBark= True)[5]
                    
                    R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_ros
                    ba         -= self.DERIVED_TREES[t].ba * removed_rate_ros
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_ros)
                    
                    n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_ros
                    trees_dict = n_tree
                    
                    BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_ros
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_ros
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_ros
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_ros
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_ros
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_ros
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_ros
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_ros
                    
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                    
                    R_SSaw, R_SPulp, R_PSaw,R_PPulp  = 0., 0., 0., 0.

                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree 
                    N_removed = 0.
                    R_vol_ros  = R_vol_ros
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp   = 0., 0., 0., 0., 0., 0.
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict = n_tree 
                N_removed = 0.
                R_vol_ros  = R_vol_ros
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp   = 0., 0., 0., 0., 0., 0.            

                    
        elif self.DERIVED_TREES[t].species == "warm":  
            if (R_vol_warm >= self.DERIVED_TREES[t].vol_warm) and (R_BA >= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,n_tree, aboveBark= True)[6]
                R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,n_tree, aboveBark= True)[6]
                R_vol_warm -= self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                BGB              -= self.DERIVED_TREES[t].BGB
                Tot_co2          -= self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      -= self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     -= self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems -= self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots -= self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    -= self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    -= self.DERIVED_TREES[t].Tot_co2_roots 
                
                G_before -= GrowthModel.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                N_removed -= self.DERIVED_TREES[t].n_tree
                R_BA -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree
                ba   -= self.DERIVED_TREES[t].ba
                n_tree =  0.
                trees_dict = n_tree
                volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SSaw, R_SPulp, R_PSaw, R_PPulp = 0., 0., 0., 0., 0., 0., 0., 0., 0., 0., 0.

            elif (R_vol_warm < self.DERIVED_TREES[t].vol_warm) and (R_BA < self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree ):
                removed_rate   = N_removed/self.DERIVED_TREES[t].n_tree
                remaining_rate = 1 - removed_rate
                removed_rate_warm   = R_vol_warm/self.DERIVED_TREES[t].vol_warm
                remaining_rate_warm = 1 - removed_rate_warm
                
                if removed_rate_warm != 0. and (self.DERIVED_TREES[t].ba >= 0):
                    N_removed   = self.DERIVED_TREES[t].n_tree * removed_rate_warm
                    R_HPulp = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[4] * self.tree_volume(t,N_removed, aboveBark= True)[6]
                    R_HSaw = self.fTimberProducts(t, self.DERIVED_TREES[t].dbh , self.DERIVED_TREES[t].height)[5] * self.tree_volume(t,N_removed, aboveBark= True)[6]
                    R_vol_warm -= self.tree_volume(t, N_removed, aboveBark= True)[6]
                    
                    R_BA       -= self.DERIVED_TREES[t].ba * self.DERIVED_TREES[t].n_tree * removed_rate_warm
                    ba         -= self.DERIVED_TREES[t].ba * removed_rate_warm
                    G_before -= GrowthModel.DERIVED_TREES[t].ba * (self.DERIVED_TREES[t].n_tree * removed_rate_warm)
                    
                    n_tree = self.DERIVED_TREES[t].n_tree * remaining_rate_warm
                    trees_dict = n_tree
                    
                    BGB              = self.DERIVED_TREES[t].BGB * remaining_rate_warm
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2 * remaining_rate_warm
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass * remaining_rate_warm
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  * remaining_rate_warm
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems * remaining_rate_warm
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots * remaining_rate_warm
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems * remaining_rate_warm
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots * remaining_rate_warm
                    
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]                     
                    
                    R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0.

                else:
                    n_tree = self.DERIVED_TREES[t].n_tree * 1.
                    trees_dict = n_tree 
                    N_removed = 0.
                    R_vol_warm = R_vol_warm
                    G_before     = G_before
                    R_BA         = R_BA
                    ba           = self.DERIVED_TREES[t].ba
                    BGB              = self.DERIVED_TREES[t].BGB
                    Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                    Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                    Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                    Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                    Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                    Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                    Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                    volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                    vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                    vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                    vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                    vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                    vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                    vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                    
                    R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0. 
            else:
                n_tree = self.DERIVED_TREES[t].n_tree * 1.
                trees_dict = n_tree 
                N_removed = 0.
                R_vol_warm = R_vol_warm
                G_before     = G_before
                R_BA         = R_BA
                ba           = self.DERIVED_TREES[t].ba
                BGB              = self.DERIVED_TREES[t].BGB
                Tot_co2          = self.DERIVED_TREES[t].Tot_co2
                Tot_biomass      = self.DERIVED_TREES[t].Tot_biomass
                Total_carbon     = self.DERIVED_TREES[t].Total_carbon  
                Tot_carbon_stems = self.DERIVED_TREES[t].Tot_carbon_stems 
                Tot_carbon_roots = self.DERIVED_TREES[t].Tot_carbon_roots 
                Tot_co2_stems    = self.DERIVED_TREES[t].Tot_co2_stems
                Tot_co2_roots    = self.DERIVED_TREES[t].Tot_co2_roots 
                volsum     = self.tree_volume(t, n_tree, aboveBark= True)[0]
                vol_spruce = self.tree_volume(t, n_tree, aboveBark= True)[1]
                vol_pine   = self.tree_volume(t, n_tree, aboveBark= True)[2]
                vol_birch  = self.tree_volume(t, n_tree, aboveBark= True)[3]
                vol_others = self.tree_volume(t, n_tree, aboveBark= True)[4]
                vol_ROS    = self.tree_volume(t, n_tree, aboveBark= True)[5]
                vol_warm   = self.tree_volume(t, n_tree, aboveBark= True)[6]
                
                R_HSaw, R_HPulp, R_SSaw, R_SPulp, R_PSaw, R_PPulp  = 0., 0., 0., 0., 0., 0.  

        return N_removed, R_vol_birch, R_vol_others, R_vol_ros, R_vol_warm, trees_dict, volsum, vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, R_SPulp, R_SSaw, R_HSaw, R_HPulp, R_PSaw, R_PPulp, G_before, R_BA, ba, BGB,Tot_co2,Tot_biomass,Total_carbon, Tot_carbon_stems,Tot_carbon_roots, Tot_co2_stems, Tot_co2_roots
                
                                                # %%%%%%                   
    
    def plot_DiameterClass(self, **kwargs):
        """
        Plot the simulated diameter class of trees for each plot
        Run this line in main.py    GrowthModel.plot_DiameterClass(GrowthModel.DERIVED_TREES)

        Parameters
        ----------
        DiameterClass list
            The diamater class list of each plot.

        Returns
        -------
        visualize the diameter class of the simulated trees in each plot

        """
        n=40
        dbhlist= [[] for _ in range(n)]
           
        plt.figure()
        plt.figure(figsize=(14,6))

        for i in range(40):      
            dbhlist[i] = [b for a,b in GrowthModel.DiameterClass if a == i+1]
            
#        plt.hist(dbhlist[0:40], bins=range(5,100,5), stacked = True, color = ['r', 'w','g','k', 'y', 'b', 'm', 'c', 'navy', 'orange', 'teal','khaki', 'hotpink', 'greenyellow', 'coral',
#                                                                             'salmon','maroon', 'indigo','forestgreen', 'violet','cyan', 'gold', 'plum', 'royalblue', 'darkred', 'fuchsia', 
#                                                                             'tan','olive','gray', 'brown', 'chocolate','cornsilk','beige','aqua','lime','burlywood','deeppink','silver',
#                                                                             'darkgreen','darksalmon'], edgecolor='black', align='left')#linewidth=1.2)
        
        plt.hist(dbhlist[0], bins=range(5,100,5), color='crimson', edgecolor='black',align='left', linewidth=1.2)        
        plt.xticks(range(5,100,5))
        # Labels & Titles for the Histogram
        plt.xlabel('Diameter class (cm) simulated in 40th period (p200)')
        plt.title('Diameter Distribution - Site Index = 11 m - plot_id = B110182')
        plt.ylabel('N / ha')
        # # Enables Grids on the Histogram Graph
        plt.grid(axis='y')
#        plt.grid(True)
        #  # Displays the Histogram
        plt.show()
#        plt.savefig('hmag_histogram.eps', facecolor='w', edgecolor='w', format='eps')

        return plt
    
    def plot_treeheight(self, **kwargs):
        """
        plot the simulated height of trees for each plot
        Run this line in main.py    GrowthModel.plot_treeheight(GrowthModel.DERIVED_TREES)

        Parameters
        ----------
        treeheight list
            The tree height list of each plot.

        Returns
        -------
        visualize the height of trees in each plot

        """
        stats = GrowthModel.Instances
#       This will find the tallest observation height 
        tallest_val = max(stats.items(), key=operator.itemgetter(1))[1]/10
        tallest_key = max(stats.items(), key=operator.itemgetter(1))[0]
#        print(tallest_val)
                
        plt.figure(figsize=(18.5,10.5))
   
        heightlist = [height/10 for p,height in GrowthModel.Treeheight]
        periodList0 = [p for p,height in GrowthModel.Treeheight]
        # This remove the repeated items from periodList0 and make them in order
        periodList= list(OrderedDict.fromkeys(periodList0))
#        print(len(periodList0))
        a=0
        b=int(len(periodList0))
        c=int(len(periodList0)/40)
        trees = [str(k) for k in GrowthModel.DERIVED_TREES.keys()]
        for sim in range(c):
            plt.plot(periodList0[a:b:c],heightlist[a:b:c], label= trees[sim])
            a+=1
            
#        labelLines(plt.gca().get_lines(),zorder=2.5)
        
        plt.axhline(y= tallest_val, color='r', linestyle='--')  
        plt.text(0, tallest_val, tallest_key)
        for k in trees:
            plt.title('Height Growth - Plot_id : '+GrowthModel.DERIVED_TREES[k].plot_id)
            break
        plt.xlabel('age (years)')
        plt.ylabel('Height of tree (in meter)')
        plt.legend(loc='best')
        plt.show()
#        plt.savefig('hmag_histogram.png', facecolor='w', edgecolor='w', format='png')
        return plt
    
    def plot_treeVolume(self, **kwargs):
        """
        Plot the simulated volume of each trees for each plot
        Run this line in main.py    GrowthModel.plot_treeVolume(GrowthModel.DERIVED_TREES)

        Parameters
        ----------
        treevolume list
            The tree volume list of each plot.

        Returns
        -------
        visualize the volume of trees in each plot

        """
#        print(GrowthModel.volume) # dm3      
        plt.figure(figsize=(18.5,10.5))
   
        volumelist = [vol/1000 for p,vol in GrowthModel.volume]
        periodList0 = [p for p,vol in GrowthModel.volume]
        # This remove the repeated items from periodList0 and make them in order
        periodList= list(OrderedDict.fromkeys(periodList0))
#        print(len(periodList0))
        a=0
        b=int(len(periodList0))
        c=int(len(periodList0)/40)
        trees = [str(k) for k in GrowthModel.DERIVED_TREES.keys()]
        for sim in range(c):
            plt.plot(periodList0[a:b:c],volumelist[a:b:c], label= trees[sim])
            a+=1
            
        labelLines(plt.gca().get_lines(),zorder=2.5)
        
        for k in trees:
            plt.title('Volume - Plot_id : '+GrowthModel.DERIVED_TREES[k].plot_id)
            break
        plt.xlabel('age (years)')
        plt.ylabel('Volume (cubic meters per hectare)')
#        plt.legend(loc='best')
        plt.show()
        
        return plt
    
    def subplot_treeheight(self, **kwargs):
        """
        Build subplots for the simulated height of trees in each plot
        Run this line in main.py    GrowthModel.subplot_treeheight(GrowthModel.DERIVED_TREES)

        Parameters
        ----------
        treeheight list
            The tree height list of each plot.

        Returns
        -------
        visualize the height of trees in each plot

        """
        stats = GrowthModel.Instances
#       This will find the tallest observation height 
        tallest_val = max(stats.items(), key=operator.itemgetter(1))[1]/10
        tallest_key = max(stats.items(), key=operator.itemgetter(1))[0]

                
        heightlist = [height/10 for p,height in GrowthModel.Treeheight]
        periodList0 = [p for p,height in GrowthModel.Treeheight]
        periodList= list(OrderedDict.fromkeys(periodList0))
        # define a list of trees to plot
        trees = [str(k) for k in GrowthModel.DERIVED_TREES.keys()]

        a= 0
        b=int(len(periodList0))
        c=int(len(periodList0)/40)
        # define the figure size and grid layout properties
        fig = plt.figure(figsize=(18.5,10.5))
        cols = 3
        gs = gridspec.GridSpec(len(trees) // cols + 1, cols)
        gs.update(hspace=0.4)

        axs = []
        for i, num in enumerate(trees):
            row = (i // cols)
            col = i % cols
            axs.append(fig.add_subplot(gs[row, col]))
            axs[-1].plot(periodList0[a:b:c],heightlist[a:b:c], label= trees[int(i)])
            
            labelLines(plt.gca().get_lines(),zorder=2.5)
            plt.axhline(y= tallest_val, color='r', linestyle='--') 
#            plt.text(0, tallest_val, tallest_key)
            plt.xlabel('age (years)')
            plt.ylabel('Height (m)')
            a+=1
                   
        plt.show()
        
        return plt

    def subplot_treeVolume(self, **kwargs):
        """
        Build subplots for the simulated volume of trees in each plot
        Run this line in main.py    GrowthModel.subplot_treeVolume(GrowthModel.DERIVED_TREES)

        Parameters
        ----------
        treevolume list
            The tree volume list of each plot.

        Returns
        -------
        visualize the volume of trees in each plot

        """
        volumelist = [vol/1000 for p,vol in GrowthModel.volume]
        periodList0 = [p for p,vol in GrowthModel.volume]
        
        # This remove the repeated items from periodList0 and make them in order
        periodList= list(OrderedDict.fromkeys(periodList0))
                
        # define a list of trees to plot
        trees = [str(k) for k in GrowthModel.DERIVED_TREES.keys()]

        a= 0
        b=int(len(periodList0))
        c=int(len(periodList0)/40)
        # define the figure size and grid layout properties
        fig = plt.figure(figsize=(18.5,10.5))
        cols = 3
        gs = gridspec.GridSpec(len(trees) // cols + 1, cols)
        gs.update(hspace=0.4)

        axs = []
        for i, num in enumerate(trees):
            row = (i // cols)
            col = i % cols
            axs.append(fig.add_subplot(gs[row, col]))
            axs[-1].plot(periodList0[a:b:c],volumelist[a:b:c], label= trees[int(i)])
            
            labelLines(plt.gca().get_lines(),zorder=2.5)
            plt.xlabel('age (years)')
            plt.ylabel('Volume (m3/ha)')
            a+=1
                   
        plt.show()
        
        return plt
    
    def Statistics(self, **kwargs):
        """
        Run this line in main.py    GrowthModel.Statistics(GrowthModel.DERIVED_TREES)  

        Parameters
        ----------
        **kwargs : none

        Returns 
        -------
        None. but yu can redirect stdin to stdout (redirect stdin to a File)
        to do this: run this line in main.py    GrowthModel.Statistics(GrowthModel.DERIVED_TREES) 
        then via Anaconda prompt run:
        $ PATH + module name >> filename.txt
        """
        trees = [str(k) for k in GrowthModel.DERIVED_TREES.keys()]
        for k in trees:
            print("\n-------------------------->> Plot_id : "+GrowthModel.DERIVED_TREES[k].plot_id + " <<-----------------------------------\n")
            break
        for i in range(1,41):
            print('\n-------------------------->> Period  :' +  str(i) + ' <<-----------------------------------\n')
            d = dict(GrowthModel.Tree_dbh[i])
            h = dict(GrowthModel.Tree_height[i])
            v = dict(GrowthModel.Tree_volume[i])
            print("\nBollandsas and Erik Næsset (2009)\n")
            print('Minimum  simulated dbh is {}  mm and its tree_id is <<{}>>'.format(min(d.items(), key=operator.itemgetter(1))[1], min(d.items(), key=operator.itemgetter(1))[0]))
            print('Maximum  simulated dbh is {}  mm and its tree_id is <<{}>>'.format(max(d.items(), key=operator.itemgetter(1))[1], max(d.items(), key=operator.itemgetter(1))[0]))
            print('Mean     simualted dbh is {} mm '.format(round(statistics.mean(d[k] for k in d))))
            print('Variance simualted dbh is {}  '.format(round(statistics.variance(d[k] for k in d))))
            print('SD       simualted dbh is {} mm '.format(round(statistics.stdev(d[k] for k in d)))) 
            print("\n")
            print('Minimum  simulated  height is {} dm and its tree_id is <<{}>>'.format(min(h.items(), key=operator.itemgetter(1))[1], min(h.items(), key=operator.itemgetter(1))[0]))
            print('Maximum  simulated  height is {} dm and its tree_id is <<{}>>'.format(max(h.items(), key=operator.itemgetter(1))[1], max(h.items(), key=operator.itemgetter(1))[0]))
            print('Mean     simualted  height is {} dm '.format(round(statistics.mean(h[k] for k in h))))
            print('Variance simualted height is {}  '.format(round(statistics.variance(h[k] for k in h))))
            print('SD       simualted height is {} dm '.format(round(statistics.stdev(h[k] for k in h))))
            print("\n")
            print('Minimum  simulated  volume is {}  dm3 and its tree_id is <<{}>>'.format(min(v.items(), key=operator.itemgetter(1))[1], min(v.items(), key=operator.itemgetter(1))[0]))
            print('Maximum  simulated  volume is {}  dm3 and its tree_id is <<{}>>'.format(max(v.items(), key=operator.itemgetter(1))[1], max(v.items(), key=operator.itemgetter(1))[0]))
            print('Mean     simualted  volume is {} dm3 '.format(statistics.mean(v[k] for k in v),2))
            print('Variance simualted volume is {}  '.format(round(statistics.variance(v[k] for k in v))))
            print('SD       simualted volume is {} dm3 '.format(round(statistics.stdev(v[k] for k in v))))
            
        return True

