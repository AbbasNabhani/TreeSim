                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
__author__ = "Abbas Nabhani && Hanne Kathrine Sjolie"                                                                                       ###
__created_on__ = "Sat Apr  4 18:22:00 2020"                                                                                                 ###
__email__ = "abbas.nabhani@gmail.com"                                                                                                       ###
__status__ = "Development of distance-independent individual tree simulator"                                                                ###                                                                                                                 
output_type = "Growth & yield curve"                                                                                                        ###
### Last Edit: 07 May 2022                                                                                                                  ###
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


class ItemTD(object): 
    def __init__(self,plot_id,tree_id,tree_sp,dbh,mort, height,diameter_class,tree_Factor,volume, Inc,Biomass, SI_spp,SI_m, t_age, volsum,
                 vol_spruce, vol_pine, vol_birch, vol_others, vol_ROS, vol_warm):
        self.plot_id=plot_id
        self.tree_id = tree_id
        self.tree_sp = tree_sp
        self.dbh = dbh
        self.mort = mort
        self.height = height
        self.diameter_class = diameter_class
        self.tree_Factor = tree_Factor
        self.volume = volume
        self.Inc = Inc
        self.Biomass = Biomass
        self.SI_spp = SI_spp
        self.SI_m = SI_m
        self.t_age = t_age
        self.volsum = volsum
        self.vol_spruce = vol_spruce
        self.vol_pine = vol_pine
        self.vol_birch = vol_birch
        self.vol_others = vol_others
        self.vol_ROS = vol_ROS
        self.vol_warm = vol_warm

