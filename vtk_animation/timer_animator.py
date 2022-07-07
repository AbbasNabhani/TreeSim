# -*- coding: utf-8 -*-

                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
__author__ = "Abbas Nabhani && Hanne Kathrine Sjolie"                                                                                       ###
__created_on__ = "Sat Apr  4 18:22:00 2020"                                                                                                 ###
__email__ = "forsim@inn.no"                                                                                                                 ###
__status__ = "Development of distance-independent individual tree simulator"                                                                ###  
__version__ = "v0.1.0"                                                                                                                      ###                                                                                                                                                                                                                            
output_type = "3D visualization and animation of the simulated results"                                                                     ###
### Last Edit: 07 May 2022                                                                                                                  ###
                                                # %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


class vtkTimerCallback():
    def __init__(self):
        self.count = 0
        self.actors = []
        self.timerId = None
        self.years = []

    def execute(self, obj, event):
        if (self.count < self.limit): 
            pass           

            if((self.count % 10) == 0 and self.count > 0):
                pass
            iren = obj
            iren.GetRenderWindow().Render()
        else:
            iren = obj
            iren.GetRenderWindow().Render()
        
        if (self.count < self.limit + 40):
            self.count = self.count + 1
        else:
            self.count = 0 
            iren = obj
            iren.GetRenderWindow().Render()
            
