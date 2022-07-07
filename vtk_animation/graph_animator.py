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
import math
from operator import itemgetter
import numpy as np
from collections import defaultdict


class Tree_Object():
    """ Describes a tree object"""
    def __init__(self, plot_data, coord, i , year):
        """Initialization of the tree objects

        Data of the variables are given in the Data dictionary
        """
        self.year = year
        self.tree_objects = plot_data['tree_objects']
        self.tree_id = self.tree_objects[i].TreeID
        self.period = self.tree_objects[i].Period
        self.coord = coord
        # stem
        self.stem_radius = self.tree_objects[i].dbh/2
        self.stem_height = self.tree_objects[i].height 
        # crown
        self.crown_height = self.tree_objects[i].CH /20
        self.crown_radius = self.tree_objects[i].MCR/2          
        
        self.species = self.tree_objects[i].species        
        self.n_tree = self.tree_objects[i].n_tree 
        self.SI = self.tree_objects[i].SI_m
        self.volsum = self.tree_objects[i].volsum          
        self.scale = 1

class GraphAnimator():
    
    def __init__(self, plot_data, timer):
        """Initialize the GraphAnimator

        Creates empty lists for actors and trees.
        One tree have two actors. One for the stem cylinder
        and another one for the crown cylinder.

        """
        
        self.plot_data = plot_data
        self.timer = timer
        self.TreeIDs = self.plot_data['treeIDs']
        self.tree_objects = self.plot_data['tree_objects']
        self.trees = []
        self.Years = self.plot_data['Years']

    def create_grid(self):
        """ 
        Creates a 3D grid and slices the grid to a 2D grid of gridsize_x and gridsize_z are used to generate to grid for the forest ground.

        """
        
        # create a grid
        xCoords = vtk.vtkFloatArray()
        for x, i in enumerate(np.linspace(0, self.plot_data['gridsize_x']+1, self.plot_data['gridsize_x']+1)):
            xCoords.InsertNextValue(i)

        zCoords = vtk.vtkFloatArray()
        for z, i in enumerate(np.linspace(0, self.plot_data['gridsize_z']+1, self.plot_data['gridsize_z']+1)):
            zCoords.InsertNextValue(i)
            

        # The coordinates are assigned to the rectilinear grid. Make sure that
        # the number of values in each of the XCoordinates, YCoordinates,
        # and ZCoordinates is equal to what is defined in SetDimensions().

        
        rgrid = vtk.vtkRectilinearGrid()
        rgrid.SetDimensions(x+1, 1, z+1)

        rgrid.SetXCoordinates(xCoords)
        rgrid.SetYCoordinates(xCoords)
        rgrid.SetZCoordinates(zCoords)
        
        ##Adding a new Filter+Mapper+Actor to visualize the grid
        # geometry filter to view the background grid
        # plane


        plane = vtk.vtkRectilinearGridGeometryFilter()

        #vtk.vtkStructuredGridGeometryFilter ()
        plane.SetInputData(rgrid)
        plane.SetExtent(0, x, 0, 0, 0, z) 
        
        # do not forget to call "Update()" at the end of the reader
        plane.Update()
        
        
        return rgrid       

    def create_axis(self):

        origin = [0, 0, 0]
        x_axis = [61, 0, 0]
        y_axis = [0, 66, 0]
        z_axis = [0, 0, 61]

        #create vtkPoints to store the points
        points = vtk.vtkPoints()
        points.InsertNextPoint(origin)
        points.InsertNextPoint(x_axis)
        points.InsertNextPoint(y_axis)
        points.InsertNextPoint(z_axis)
        #set colors of lines
        red = [255, 0, 0]
        green = [0, 255, 0]
        blue = [0, 0, 255]

        #colors array
        colors = vtk.vtkUnsignedCharArray()
        colors.SetNumberOfComponents(3)
        colors.SetName("Colors")

        #Add colors to the color's array
        colors.InsertNextTypedTuple(red)    
        colors.InsertNextTypedTuple(green) 
        colors.InsertNextTypedTuple(blue)

        #Create lines
        x_line = vtk.vtkLine()
        x_line.GetPointIds().SetId(0,0)
        x_line.GetPointIds().SetId(1,1)
        
        y_line = vtk.vtkLine()
        y_line.GetPointIds().SetId(0,0)
        y_line.GetPointIds().SetId(1,2)
        
        z_line = vtk.vtkLine()
        z_line.GetPointIds().SetId(0,0)
        z_line.GetPointIds().SetId(1,3)

        #cellArray to store lines
        axis = vtk.vtkCellArray()
        axis.InsertNextCell(x_line)
        axis.InsertNextCell(y_line)
        axis.InsertNextCell(z_line)
        
        #create Polydata to store everything
        axisPolyData = vtk.vtkPolyData()
        #add the points
        axisPolyData.SetPoints(points)
        #add the lines
        axisPolyData.SetLines(axis)
        #color them
        axisPolyData.GetCellData().SetScalars(colors)
        
        
        return axisPolyData
    
    def get_boundaries(self, data_list):                                       ## OK
        
        x_max = 0
        x_min = 0
        y_max = 0
        y_min = 0
        
        for data in data_list:
            xmax = max(data, key=itemgetter(0))[0]
            xmin = min(data, key=itemgetter(0))[0]
            ymax = max(data, key=itemgetter(1))[1]
            ymin = min(data, key=itemgetter(1))[1]
            #print((xmax,xmin,ymax,ymin))
            
            if(xmax > x_max or x_max == 0):
                x_max = xmax
            if(xmin < x_min or x_min == 0):
                x_min = xmin
            if(ymax > y_max or y_max == 0):
                y_max = ymax
            if(ymin < y_min or y_min == 0):
                y_min = ymin
        
        return [x_max, x_min, y_max, y_min]
    
    
    def initialize_trees(self, renderer):
        self.get_actors = TreeScene(self.plot_data, renderer, self.timer, self.trees)
        self.get_actors.create_actors(self.plot_data['number_of_trees'], self.timer)
            
        self.get_actors.manage_actors(self.timer)


class TreeScene:
    def __init__(self, plot_data, renderer, year, trees):

        self.year = year
        self.plot_data = plot_data
        self.treeIDs  = plot_data['treeIDs']        
        self.tree_objects = plot_data['tree_objects']
        self.renderer = renderer
        self.trees = trees
        self.tree_actors = []

        self.stem_del, self.crown_del, self.tree_del = [], [], []

    def create_actors(self, number_of_trees, year):
        
        ### initialize trees
        before_treelenght = len(self.trees)
        # X and Y of tree coordinates
        np.random.seed(1)
        for i in self.treeIDs:
            
            coord_x = self.tree_objects[i].coord_x 
            coord_z = self.tree_objects[i].coord_z
            
            coord = coord_x * self.plot_data['gridsize_x']/20, coord_z * self.plot_data['gridsize_z']/20
            
            tree_i = Tree_Object(self.plot_data, coord, i, year)
            self.trees.append(tree_i)
        ### initialize actors
        before_actorlength = len(self.tree_actors)
        
        for i in range(before_treelenght, len(self.trees)):
            
            """ stem  """

            r = np.random.randint(6,10)/10
            brown_color = (r, r*0.6, r*0.2)
            birch_color = (r, r*0.8, r*0.66666666666666666666)
            
            if self.trees[i].species == "scots_pine" or self.trees[i].species == "spruce":
                stem_actor = Cylinder(self.trees[i].stem_radius, self.trees[i].stem_height, ( self.trees[i].coord[0], self.trees[i].stem_height, self.trees[i].coord[1] ), brown_color ).cylinder_actor()
                self.tree_actors.append(stem_actor)
            else:
                stem_actor = Cylinder(self.trees[i].stem_radius, self.trees[i].stem_height, ( self.trees[i].coord[0], self.trees[i].stem_height, self.trees[i].coord[1] ), birch_color ).cylinder_actor()
                self.tree_actors.append(stem_actor)                

            """ crown  """

            if self.trees[i].n_tree >= 1:
                green_color = (0, np.random.randint(3,10)/10, 0)

            elif self.trees[i].n_tree < 1: 
                green_color = (1, np.random.randint(3,10)/10, 0)
            
            if self.trees[i].species == "scots_pine" or self.trees[i].species == "spruce":         
                                
                crown_actor = Cone(self.trees[i].crown_radius, self.trees[i].crown_height, ( self.trees[i].coord[0], self.trees[i].crown_height, self.trees[i].coord[1] ), green_color).cone_actor()
                self.tree_actors.append(crown_actor)                
            else: 
                crown_actor = Cylinder(self.trees[i].crown_radius, self.trees[i].crown_height, ( self.trees[i].coord[0], self.trees[i].crown_height, self.trees[i].coord[1] ), green_color ).cylinder_actor()
                self.tree_actors.append(crown_actor)


        # Add all tree actors to the renderer
        for i in range(before_actorlength, len(self.tree_actors)):
            self.renderer.AddViewProp(self.tree_actors[i])
            
        return self.tree_actors
    
    
    def manage_actors(self, step):
        for i in range(len(self.trees)):
            # iterator index
            stem_i = (i + 1) * 2 - 2
            crown_i = (i + 1) * 2 - 1
            self.Set_Position(i, stem_i, crown_i, step)
            self.is_tree_death(stem_i, crown_i, i)

        self.Removal()


    def Set_Position(self, i, stem_i, crown_i, step):
        
        self.trees[i].period += 1        
        scale = self.trees[i].scale * 2
        # Set_Position of stem
        self.tree_actors[stem_i].SetScale(scale)
        stem_pos = list(self.tree_actors[stem_i].GetPosition())
        stem_pos[1] =  self.trees[i].stem_height * scale / 2
        self.tree_actors[stem_i].SetPosition(stem_pos)
        # Set_Position of crown
        self.tree_actors[crown_i].SetScale(scale)
        crown_pos = list(self.tree_actors[crown_i].GetPosition())
        crown_pos[1] = self.trees[i].stem_height * scale
        self.tree_actors[crown_i].SetPosition(crown_pos)
            

    def is_tree_death(self, stem_i, crown_i, i):
        ### Removal
        n_tree = self.trees[i].n_tree
        if n_tree == 0:

            self.tree_del.insert(0, i)
            self.stem_del.insert(0, stem_i)
            self.crown_del.insert(0, crown_i)

    def Removal(self):
        for index in range(0, len(self.tree_del)):
            self.renderer.RemoveViewProp(self.tree_actors[self.stem_del[index]])
            self.renderer.RemoveViewProp(self.tree_actors[self.crown_del[index]])
            del self.trees[self.tree_del[index]]
            del self.tree_actors[self.crown_del[index]]
            del self.tree_actors[self.stem_del[index]]

        self.stem_del, self.crown_del, self.tree_del = [], [], []


class Cylinder():
    def __init__(self, radius, height, loc, color, opacity=1):
        self.radius = radius
        self.height = height
        self.loc = loc
        self.color = color
        self.opacity = opacity


    def cylinder_actor(self):

        cylinder = vtk.vtkCylinderSource()
        cylinder.SetResolution(800)
        cylinder.SetRadius(self.radius)
        cylinder.SetHeight(self.height)

        mapper = vtk.vtkPolyDataMapper()
        mapper.SetInputConnection(cylinder.GetOutputPort())

        actor = vtk.vtkActor()
        actor.SetMapper(mapper)
        actor.SetPosition(self.loc)
        actor.GetProperty().SetColor(self.color)
        actor.GetProperty().SetOpacity(self.opacity)

        return actor
    
    
class Cone():
    def __init__(self, radius, height, loc, color, opacity=1):
        self.radius = radius
        self.height = height
        self.loc = loc
        self.color = color
        self.opacity = opacity


    def cone_actor(self):

        cone = vtk.vtkConeSource()
        cone.SetResolution(900)
        cone.SetRadius(self.radius)
        cone.SetHeight(self.height)

        transform = vtk.vtkTransform()
        transform.RotateWXYZ(90, 0, 0, 1)
        transformFilter = vtk.vtkTransformPolyDataFilter()
        transformFilter.SetTransform(transform)
        transformFilter.SetInputConnection(cone.GetOutputPort())
        transformFilter.Update()

        mapper = vtk.vtkPolyDataMapper()
        mapper.SetInputConnection(transformFilter.GetOutputPort())

        # actor (Actor for opacity as a property value.)
        actor = vtk.vtkActor()        
        actor.SetMapper(mapper)
        actor.SetPosition(self.loc)
        actor.GetProperty().SetColor(self.color)
        actor.GetProperty().SetOpacity(self.opacity)
        
        return actor
    

