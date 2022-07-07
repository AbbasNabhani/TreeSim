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

import vtk
import json
import random
from operator import itemgetter
import timer_animator
import graph_animator 
import os 
import sys
import numpy as np
import time
import math
from collections import defaultdict
import glob
import moviepy.editor as mpy
import shutil




json_file_name = "/A94962_scenario21_tree_simulation.json"

tree_objects = defaultdict(lambda:defaultdict(int))
plot_data = dict()
timer = dict()
DictTree = defaultdict(list)



def current_working_directory(directory):
    if(os.path.exists(directory)):
        os.chdir(directory)
        cwd = os.getcwd()
    return cwd

def mkdir(name):
    if not os.path.exists(name):
        os.mkdir(name)
    assert os.path.isdir(name) 
    
    
def close_window(iren):
    renderWindow = iren.GetRenderWindow()
    renderWindow.Finalize()
    iren.TerminateApp()
    del renderWindow, iren
        
def get_treeIDs(directory):
        
#    data = [json.loads(line) for line in open(current_working_directory(directory)+"/tree_simulation.json", 'r')]
    
    trees = []
    treeIDs = defaultdict(list)
    
    with open(current_working_directory(directory)+json_file_name) as infile:
        data = json.load(infile)

    for item in data:
        tree_id         = int(item["tree_id"])
        if tree_id not in trees:
            trees.append(tree_id)
        
        year            = int(item["year"])+1
        if tree_id in treeIDs[year]:
            treeIDs[year] = [tree_id]
        else:
            treeIDs[year].append(tree_id)
  
    return trees, treeIDs

def get_data(directory, years):
    
    with open(current_working_directory(directory)+json_file_name) as infile:
        data = json.load(infile)
    
    
        for item in data:
            
            PlotID          = item["plot_id"]
            TreeID          = int(item["tree_id"])
            tree_sp         = int(item["tree_sp"])
            dbh             = float(item["dbh"])/1000    # convert to meter from mm
            height          = float(item["height"])/10   # convert to meter from dm
            diameter_class  = int(item["diameter_class"])
            tree_Factor     = float(item["tree_Factor"])
            SI_spp          = int(item["SI_spp"])
            SI_m            = int(item["SI_m"])
            n_tree          = float(item["n_tree"])
            species         = item["species"]    
            Period          = int(item["Period"])  
            coord_x         = float(item["coord_x"])
            coord_z         = float(item["coord_y"])
            year            = int(item["year"])+1   # +1 can be deleted, we did this to make the years 
            volsum          = float(item["volsum"])
            management      = item["management"]
            CH              = (4.1203 - 0.002817*(dbh*100)*(dbh*100) + 0.26234*height*height - 0.3184*((dbh*100)/height)*((dbh*100)/height))   # Crown height of pine (m) reference "https://github.com/hansoleorka/skogR"
            MCR             = (1.03881 + 0.06024 * (dbh*100))  # mean crown radius (m) reference : Crown Radius and Diameter at Breast Height Relationships for Six Bottomland Hardwood Species, Lockhart R. B. et. al.
                           
            tree_objects[year][TreeID] = treeObj(PlotID,TreeID,tree_sp, dbh ,height,diameter_class,tree_Factor, SI_spp,SI_m, n_tree, species , Period, coord_x, coord_z, volsum, CH, MCR, year, management)            

            if (year not in years):
                years.append(year)  

            if TreeID in DictTree[year]:
                DictTree[year] = [TreeID]
            else:
                DictTree[year].append(TreeID)
              
        return years


class treeObj():
    
    def __init__(self,PlotID,TreeID,tree_sp, dbh ,height,diameter_class,tree_Factor, SI_spp,SI_m, n_tree, species , Period, 
                 coord_x, coord_z, volsum, CH, MCR, year, management):
        
        self.PlotID = PlotID
        self.TreeID = TreeID
        self.tree_sp = tree_sp
        self.dbh=dbh
        self.height=height
        self.diameter_class = diameter_class
        self.tree_Factor = tree_Factor
        self.SI_spp = SI_spp
        self.SI_m = SI_m
        self.n_tree = n_tree
        self.species = species
        self.Period = Period
        self.coord_x = coord_x
        self.coord_z = coord_z
        self.volsum = volsum
        self.CH = CH
        self.MCR = MCR
        self.year = year
        self.management = management
    
    def __str__(self):
        return 'PlotID\n\t{}\n\nTreeID\n\t{}\n\ntree_sp\n\t{}\n\ndbh\n\t{}\n\nheight\n\t{}\n\ndiameter_class\n\t{}\n\ntree_Factor\n\t{}\n\nSI_spp\n\t{}\n\nSI_m\n\t{}\n\nn_tree\n\t{}\n\nPeriod\n\t{}\n\nspecies\n\t{}\n\ncoord_x\n\t{}\n\ncoord_z\n\t{}\n\nvolsum\n\t{}\n\nyear\n\t{}\n\nmanagement\n\t{}\n'.format(self.PlotID, 
                          self.TreeID, self.tree_sp, self.dbh, self.height, self.diameter_class,self.tree_Factor, self.SI_spp,self.SI_m, self.n_tree, self.Period, self.species, self.coord_x, self.coord_z, self.volsum, self.year, self.management)        
    
def main():
    

    #WORK_DIR = os.getcwd() + "/"
    
    full_path = os.path.realpath(__file__)   
    directory = os.path.dirname(full_path)
    """
    delete the folder "figures", as well as all its contents using: 
    shutil.rmtree(path, ignore_errors=False, onerror=None)
    """
    mkdir("figures") 
    
    shutil.rmtree(os.path.join(current_working_directory(directory), "figures/"))
    
    mkdir("figures") 
    
    trees   = get_treeIDs(directory)[0]
    treeIDs = get_treeIDs(directory)[1]
#    print(treeIDs[2020])
    
    years = []
    
    if(len(years) == 0):
        data_years = get_data(directory, years)
               
    else:
        data_years = get_data(directory, []) 
        

    for Year in years:
#    Year = 2020      
        plot_data[Year] = {
                            'number_of_trees' :    len(treeIDs[Year]),   
                            'treeIDs'         :    treeIDs[Year],
                            'tree_objects'    :    tree_objects[Year],
                            'Years'           :    years,
                            'gridsize_x'      :    60,               #grid length
                            'gridsize_z'      :    60                #grid width
                           } 
        
        timer[Year] = { 'years' : Year}
        
    #    print(DictTree[Year])
    #    print(plot_data[Year]['tree_objects'])    
    #    print(plot_data['tree_objects'][425930].SI_m)   
    
        ga = graph_animator.GraphAnimator(plot_data[Year], timer[Year])
    
        
        """ create plot axis"""
        axisPolyData = ga.create_axis()  
        rgrid = ga.create_grid()
        
        """ Create a mapper and actor """
        axisMapper = vtk.vtkPolyDataMapper()
        axisMapper.SetInputDataObject(axisPolyData)
        gridMapper = vtk.vtkDataSetMapper()
        gridMapper.SetInputData(rgrid)    
        axisActor = vtk.vtkActor()
        axisActor.SetMapper(axisMapper)
        grid_actor = vtk.vtkActor()
        grid_actor.SetMapper(gridMapper)
        grid_actor.GetProperty().EdgeVisibilityOn() # showing mesh
        grid_actor.GetProperty().LightingOff()
        grid_actor.GetProperty().SetColor(0.75, 0.75, 0)
        grid_actor.GetProperty().SetOpacity(0.1)  # transparency
             
        """ Setup a renderer, render window, and interactor"""
        colors = vtk.vtkNamedColors()
    
        renderer = vtk.vtkRenderer()
        #renderer.SetBackground(colors.GetColor3d('White'))
        renderer.SetBackground(colors.GetColor3d('DarkSlateGray'))
        #renderer.SetBacground(colors.GetColor3d("Wheat"))
        #renderer.SetBackground(colors.GetColor3d('MidnightBlue'))
        renderer = vtk.vtkRenderer()
        
        # vtkRenderWindow
        renderWindow = vtk.vtkRenderWindow()
        renderWindow.AddRenderer(renderer)
        renderWindow.SetSize(1920, 1080)
        renderWindow.SetWindowName('Forest-Dynamics')    
        
    #    # use StereoScopic
        renderWindow.SetFullScreen(1)
        renderWindow.SetStereoCapableWindow(1)
        renderWindow.StereoRenderOn()
        #renderWindow.SetStereoTypeToAnaglyph()
        #renderWindow.SetStereoTypeToInterlaced()
        #renderWindow.SetStereoTypeToDresden()
        renderWindow.SetStereoTypeToCrystalEyes()
        renderWindow.StereoUpdate()
    
        # create a renderwindowinteractor
        renderWindowInteractor = vtk.vtkRenderWindowInteractor()
        renderWindowInteractor.SetRenderWindow(renderWindow)
        renderWindow.Render()
        
    
        """ Add the axis actor"""
        renderer.AddActor(axisActor)    
        """ Add the grid actor """
        renderer.AddViewProp(grid_actor)
        
        txt_title = vtk.vtkTextActor()
        Year1 = str(Year)
        txt_title.SetInput(Year1)
    #    txt_title.SetInput(str(years[len(years)-1])) 
        txt_title_prop = txt_title.GetTextProperty()
        txt_title_prop.SetFontSize(60)
        txt_title_prop.SetColor(0, 0, 0)
        txt_title.SetDisplayPosition(200, 950)
        
               
        txt_z = vtk.vtkTextActor()
        txt_z.SetInput('z axis')
        txt_z_prop = txt_z.GetTextProperty()
        txt_z_prop.SetFontSize(20)
        txt_z_prop.SetColor(0, 0, 1)
        txt_z.SetDisplayPosition(480, 230)
        
        txt_x = vtk.vtkTextActor()
        txt_x.SetInput('x axis')
        txt_x_prop = txt_x.GetTextProperty()
        txt_x_prop.SetFontSize(20)
        txt_x_prop.SetColor(1, 0, 0)
        txt_x.SetDisplayPosition(1400, 230)
        
        txt_y = vtk.vtkTextActor()
        txt_y.SetInput('y axis')
        txt_y_prop = txt_y.GetTextProperty()
        txt_y_prop.SetFontSize(20)
        txt_y_prop.SetColor(0, 1, 0)
        txt_y.SetDisplayPosition(950, 1000)
        
        txt_xName = vtk.vtkTextActor()
        txt_xName.SetInput('Plot ID:')
        txt_xName_prop = txt_xName.GetTextProperty()
        txt_xName_prop.SetFontSize(30)
        txt_xName_prop.SetColor(0, 1, 0)
        txt_xName.SetDisplayPosition(70, 1040)
        
        txt_xYear = vtk.vtkTextActor()
        txt_xYear.SetInput('year')
        txt_xYear_prop = txt_xYear.GetTextProperty()
        txt_xYear_prop.SetFontSize(60)
        txt_xYear_prop.SetColor(0, 0, 0)
        txt_xYear.SetDisplayPosition(40, 950)
        
        txt_xTName = vtk.vtkTextActor()
        txt_xTName.SetInput('Tree IDs:')
        txt_xTName_prop = txt_xTName.GetTextProperty()
        txt_xTName_prop.SetFontSize(30)
        txt_xTName_prop.SetColor(0, 1, 0)
        txt_xTName.SetDisplayPosition(1600, 1040)
        
        txt_xID = vtk.vtkTextActor()
        txt_xID.SetInput(str(plot_data[Year]['tree_objects'][plot_data[Year]['treeIDs'][0]].PlotID))
        txt_xID_prop = txt_xID.GetTextProperty()
        txt_xID_prop.SetFontSize(30)
        txt_xID_prop.SetColor(0, 0, 0)
        txt_xID.SetDisplayPosition(230, 1040)
    
        txt_xF = vtk.vtkTextActor()
        txt_xF.SetInput('|______________________________________|')
        txt_xF_prop = txt_xF.GetTextProperty()
        txt_xF_prop.SetFontSize(18)
        txt_xF_prop.SetColor(0, 0, 0)
        txt_xF.SetDisplayPosition(10, 1030)
        
        
        txt_xT = vtk.vtkTextActor()
        txt_xT.SetInput('|_________________________|')
        txt_xT_prop = txt_xT.GetTextProperty()
        txt_xT_prop.SetFontSize(18)
        txt_xT_prop.SetColor(0, 0, 0)
        txt_xT.SetDisplayPosition(1530, 1030)
        
        txt_mgt_txt = vtk.vtkTextActor()
        txt_mgt_txt.SetInput('Management method:')
        txt_mgt_txt_prop = txt_mgt_txt.GetTextProperty()
        txt_mgt_txt_prop.SetFontSize(30)
        txt_mgt_txt_prop.SetColor(0, 0, 0)
        txt_mgt_txt.SetDisplayPosition(20, 90)

        txt_mgt = vtk.vtkTextActor()
        txt_mgt.SetInput(str(plot_data[Year]['tree_objects'][plot_data[Year]['treeIDs'][0]].management))
        txt_mgt_prop = txt_mgt.GetTextProperty()
        txt_mgt_prop.SetFontSize(30)
        txt_mgt_prop.SetColor(0, 0, 1)
        txt_mgt.SetDisplayPosition(380, 90)

        
        txt_actors = []
        txt_actors.append(txt_title)
    #    txt_actors.append(txt_xName)
    #    
        txt_actors.append(txt_xTName)
        txt_actors.append(txt_xID)
    #    txt_actors.append(txt_xF)
        renderer.AddActor(txt_title)
        renderer.AddActor(txt_xYear)
        renderer.AddActor(txt_z)
        renderer.AddActor(txt_x)
        renderer.AddActor(txt_y)
        renderer.AddActor(txt_xName)
        renderer.AddActor(txt_xTName)
        renderer.AddActor(txt_xID)
        renderer.AddActor(txt_xF)
        renderer.AddActor(txt_xT) 
        renderer.AddActor(txt_mgt_txt)
        renderer.AddActor(txt_mgt)
    
        actors = ga.initialize_trees(renderer)
        
        for index, ci in enumerate(plot_data[Year]['treeIDs']):
            txt_treeID = vtk.vtkTextActor()
    
            txt_treeID.SetInput(str(ci))
            txt_treeID_prop = txt_treeID.GetTextProperty()
            txt_treeID_prop.SetFontSize(22)
            #txt_treeID_prop.SetColor(colors[ci][0], colors[ci][1], colors[ci][2])
            
            if plot_data[Year]['tree_objects'][ci].n_tree >= 1:
    
                txt_treeID_prop.SetColor(0, 0, 0)
            else:
                txt_treeID_prop.SetColor(1, 0, 0)
            
            if index <= 38:                
                
                txt_treeID.SetDisplayPosition(1520, 40 + (index * 25))
            elif index <= 76:
                txt_treeID.SetDisplayPosition(1620, (index * 25) - 935)
            else:
                txt_treeID.SetDisplayPosition(1720, (index * 25) - 1870)
        
            renderer.AddActor(txt_treeID)
    
        
        """ set Camera """
        camera = vtk.vtkCamera()
        camera.SetViewUp(0,1,0)
        camera.SetPosition(0,0,-2000)
        camera.SetFocalPoint(0,0,-1500)
        #camera.SetFocalPoint(0, 0, 0)
        #    camera.Dolly(.28) 
        camera.ComputeViewPlaneNormal()
        # Set the white background
        renderer.SetBackground(1, 1, 1)
        #renderer.SetActiveCamera(camera)
        renderer.GetActiveCamera().Azimuth(45)
        renderer.GetActiveCamera().Elevation(10)
        renderer.ResetCameraClippingRange(-320,320,-240,240,0,4096)        
        renderer.ResetCamera() 
    
        """ Render and interact """
    
        renderWindow.Render()
        style = vtk.vtkInteractorStyleTrackballCamera()
        renderWindowInteractor.SetInteractorStyle(style)
        
        
        # Initialize must be called prior to creating timer events.
        renderWindowInteractor.Initialize() 
        
    
        """ SETUP TIMER EVENTS"""
        
        actrs = renderer.GetActors()
        cb = timer_animator.vtkTimerCallback()
        cb.actors = actrs
        cb.years = years
        cb.limit = 0
    
        renderWindowInteractor.AddObserver('TimerEvent', cb.execute)
        timerId = renderWindowInteractor.CreateRepeatingTimer(100)
        
    #        return renderWindowInteractor         
        renderWindowInteractor.Start()   #start the interaction and timer
        
            ## This is used to store the frames
        ## for creating a movie
    
        w2i = vtk.vtkWindowToImageFilter()
        w2i.SetInput(renderWindow)
        w2i.Update()
        
        ## The writer
        writer = vtk.vtkPNGWriter()
        filename = os.path.join(current_working_directory(directory),"figures/") + '%d.png' % Year
        writer.SetFileName(filename)
        writer.SetInputConnection(w2i.GetOutputPort())
        writer.Write() 
        
        close_window(renderWindowInteractor)  
        del renderWindow, renderWindowInteractor
        
   
    gif_name = "Tree_animation"
    fps = 1
    file_list = glob.glob(os.path.join(current_working_directory(directory),'figures/*.png')) # Get all the pngs in the current directory
    
    clip = mpy.ImageSequenceClip(file_list, fps=fps)
    clip.write_gif(os.path.join(current_working_directory(directory),"figures/{}.gif".format(gif_name)), fps=fps)   
    
if __name__ == '__main__':
   iren = main()
   #iren.Start()  
