
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
__author__ = "Abbas Nabhani && Hanne Kathrine Sjolie"                                                                                       ###
__created_on__ = "Sat Apr  4 18:22:00 2020"                                                                                                 ###
__email__ = "abbas.nabhani@gmail.com"                                                                                                       ###
__status__ = "Development of distance-independent individual tree simulator"                                                                ### 
__version__ = "v0.1.0"                                                                                                                      ###                                                                                                                                                                                                                             
output_type = "Growth & yield curve"                                                                                                        ###
### Last Edit: 07 May 2022                                                                                                                  ###
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


class TreeObject(object):
    def __init__(self,plot_id,tree_id,tree_sp,dbh,height,diameter_class,tree_Factor,SI_spp,SI_m, n_tree, species, Period, coord_x, coord_y, year, volsum,
                 vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm, management):
        self.plot_id=plot_id
        self.tree_id = tree_id
        self.tree_sp = tree_sp
        self.dbh = dbh
        self.height = height
        self.diameter_class = diameter_class
        self.tree_Factor = tree_Factor
        self.SI_spp = SI_spp
        self.SI_m = SI_m
        self.n_tree = n_tree
        self.species = species
        self.Period = Period
        self.coord_x = coord_x
        self.coord_y = coord_y
        self.year = year
        self.volsum = volsum
        self.vol_spruce = vol_spruce
        self.vol_pine = vol_pine
        self.vol_birch = vol_birch
        self.vol_others = vol_others
        self.vol_ROS = vol_ROS
        self.vol_warm = vol_warm
        self.management = management

