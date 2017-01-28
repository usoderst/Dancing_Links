
# coding: utf-8

# In[131]:

import numpy as np
from math import sqrt,ceil,pow
from time import time
import collections
import random
import os

###############################
#Define Non-Class Methods
###############################

def GenQue(filename,Nkeys):
    keyque = []
    Data_File = open(filename, "r")
    header = Data_File.readline()
    for line in Data_File:
        line_list = [x.strip() for x in line.lower().split(",")]
        if int(line_list[1]) != 0:
            keyque.append("N"+str(line_list[0]))
    for key in Nkeys:
        if key not in keyque:
            keyque.append(key)
    return keyque

def getConnectionsFromKey(node_type,ID):
    #pass in the key of any node and return a list of keys that this node should be connected to
    if node_type == 'N':
        #connects to one row, column and section
        Rid = int(ceil(ID/number_range))

        Cid = ID % number_range
        if Cid == 0: #adjust modulus
            Cid = number_range
        
        Srow = int(ceil(Rid/sqrt(number_range)))
        Scol = int(ceil(Cid/sqrt(number_range)))
        Sid = int(sqrt(number_range)*(Srow - 1) + Scol)

        return ['R'+str(Rid),'C'+str(Cid),'S'+str(Sid)]

    elif node_type == 'R':
        connections = []
        baseId = (ID - 1) * number_range + 1
        for i in range(number_range):
            connections.append('N' + str(baseId + i))
        return connections

    elif node_type == 'C':
        connections = []
        for i in range(number_range):
            connections.append('N' + str(ID + (i*number_range)))
        return connections

    elif node_type == 'S':
        connections = []
        baseRow = ceil(ID/sqrt(number_range))-1
        baseCol = int(ID % sqrt(number_range))
        if baseCol == 0: #adjust modulud
            baseCol = int(sqrt(number_range))
        baseCol -= 1
        baseId = 1 + (baseRow*number_range*sqrt(number_range)) + (baseCol*sqrt(number_range))
        for i in range(int(sqrt(number_range))):
            for j in range(int(sqrt(number_range))):
                connections.append('N' + str(int(baseId + (i*number_range) + j)))
        return connections

###############################
#Define Classes
###############################

class Vertex:
    def __init__(self,key,vertex_type,number_range,connectionKeys,value=0):
        self.id = key
        self.connectionKeys = connectionKeys
        self.number_range = number_range
        self.vertex_type = vertex_type
        self.value = value
        self.possible_values = []

class Multi_Graph:
    def __init__(self,file_name):
        self.vertList = collections.OrderedDict() #Treat like as if it was {}, contains all node types
        self.numVertices = 0
        self.numClues = 0
        self.file_name = file_name
        self.Nkeys = ['N'+str(i+1) for i in range(int(pow(number_range,2)))]
        self.Rkeys = ['R'+str(i+1) for i in range(number_range)]
        self.Ckeys = ['C'+str(i+1) for i in range(number_range)]
        self.Skeys = ['S'+str(i+1) for i in range(number_range)]

        #initialization Methods
        self.initialize_graph() #Construct the verticies and edges between them from a .csv file
        self.getPossibleValues() #initialize possible values for all non-clues
        boardComplete = self.getFreeClues() #use extrapolate() to find any polynomial-time solvable clues from the starting clues
        
        if not boardComplete:
            print('------possible values for each undetermined node------')
            self.printPossibleValues()
            print('------Basic Dancing Links------')
            self.DancingLinks([],[])
            print('------Graph!------')
            self.GraphA()

    def initialize_graph(self):    #builds the matrix and splits into row array, column array, and section array
        self.np_matrix = np.loadtxt(open(self.file_name),dtype = 'int',delimiter=",") #skiprows=1
        self.component_sub_square = int(sqrt(self.np_matrix[1,:].size))
        self.matrix_range = self.component_sub_square*self.component_sub_square
        
        #getting each column as arrays
        self.columns = []
        for i in range(0,(self.component_sub_square*self.component_sub_square)):
            self.columns.append(self.np_matrix[:,i])
            
        #getting each row as arrays
        self.row = []
        for j in range(0,(self.component_sub_square*self.component_sub_square)):
            self.row.append(self.np_matrix[j,:])
            
            
        #getting each suection from left to right then move down one set of rows
        self.sections = []
        for i in range(0, (self.component_sub_square * self.component_sub_square), self.component_sub_square): #rows
            for j in range(0, (self.component_sub_square * self.component_sub_square), self.component_sub_square): #columns
                self.sections.append(self.np_matrix[i:(i+self.component_sub_square),j:(j+self.component_sub_square)])
                
        #adding a vertex for each row type
        temp_type = 'R' #R = Row type
        node_type = 'N'
        
        counter = 1
        counter_node = 1
        for i in self.row:
            temp_id = temp_type + str(counter) #Ex. R1, R2, R3,...., Rn
            self.addVertex(temp_id,temp_type,self.matrix_range,getConnectionsFromKey(temp_type,counter))
            for j in i:
                
                node_id = node_type + str(counter_node)
                val = j
                if (j == 0):
                    self.addVertex(node_id,node_type,self.matrix_range,getConnectionsFromKey(node_type,counter_node),val=0)
                else:
                    self.addVertex(node_id,node_type,self.matrix_range,getConnectionsFromKey(node_type,counter_node),val=j)
                    self.numClues+=1
                counter_node+=1
            counter+=1
        
        #adding a vertex for each Column type
        temp_type = 'C' #C = Col type
        counter = 1
        for i in self.columns:
            temp_id = temp_type + str(counter) #Ex. C1, C2, C3,...., Cn
            self.addVertex(temp_id,temp_type,self.matrix_range,getConnectionsFromKey(temp_type,counter))
            counter+=1            
            
        #adding a vertex for each Section type
        temp_type = 'S' #S = Sec type
        counter = 1
        for i in self.sections:
            temp_id = temp_type + str(counter) #Ex. S1, S2, S3,...., Sn
            self.addVertex(temp_id,temp_type,self.matrix_range,getConnectionsFromKey(temp_type,counter))
            counter+=1

    def addVertex(self,key,vertex_type,matrix_range,connections,val=0):    #adds an instance of Vertex to the graph.
        self.numVertices = self.numVertices + 1
        self.val = val
        newVertex = Vertex(key,vertex_type,matrix_range,connections,val)

        #add vertex to appropriate Multi_Graph fields
        self.vertList[key] = newVertex
        return newVertex

    def getVertex(self,n):   #finds the vertex in the graph named vertKey.
        if n in self.vertList:
            return self.vertList[n]
        else:
            return None

    def __contains__(self,n):    #determines of graph instance contains a vertex "n" 
        return n in self.vertList

    def getVertices(self):   #returns the list of all vertices in the graph
        return self.vertList.keys()

    def __iter__(self):
        return iter(self.vertList.values())

    def getPossibleValues(self): #Gets possible values 
        #Update each node with value = 0's array of possible values
        Nkeys = ['N'+str(i+1) for i in range(int(pow(number_range,2)))]
        for nodeKey in Nkeys:
            thisNode = self.vertList[nodeKey]
            if thisNode.value == 0:

                #this section of code executes for all nodes that do not have values
                possibleValues = [i+1 for i in range(number_range)]

                #examine neighboring nodes in row, col, sec, remove their values from possibe values
                for groupKey in thisNode.connectionKeys:
                    for thisNeighbor in self.vertList[groupKey].connectionKeys:
                        neighborVal = self.vertList[thisNeighbor].value
                        if neighborVal != 0 and neighborVal in possibleValues:
                            possibleValues.remove(neighborVal)
                thisNode.possible_values = possibleValues
                # print(nodeKey + ' ' + str(possibleValues))

    def printBoard(self):
        for rowKey in self.Rkeys:
            rowString = ''
            for nodeKey in self.vertList[rowKey].connectionKeys:
                rowString += str(self.vertList[nodeKey].value)
            print(rowString)

    def extrapolate(self,nodeArrayIn,valueArrayIn):
        #method that takes in an array of nodes and an array of cooresponding values and returns a 
        #tuple containing two lists of the same format. The returned lists contain nodes that must
        #the cooresponding value if the input arguments are taken to be true

        #store the current states of nodes at this depth before testing deeper depths
        initial_values = []
        initial_posibilities = []
        initial_numClues = self.numClues

        #store each node's starting value and possible_values
        for nodeKey in self.Nkeys:
            thisNode = self.vertList[nodeKey]
            initial_values.append(thisNode.value)
            initial_posibilities.append(thisNode.possible_values)

        #build return arrays
        nodeArrayOut = nodeArrayIn[:]
        valueArrayOut = valueArrayIn[:]

        #create node keys of each type
        GroupKeys = self.Rkeys + self.Ckeys + self.Skeys

        #add the extra conditions passed in with nodeArrayIn and valueArryIn
        for i in range(len(nodeArrayIn)):
            self.vertList[nodeArrayIn[i]].value = valueArrayIn[i]

        #Check loop: if a value is found, repeat the entire checking process with the new info
        continueChecking = True
        boardComplete = False
        boardCorrect = True
        while continueChecking and not boardComplete and boardCorrect:
            self.getPossibleValues()
            continueChecking = False 

            #Process 1: check for nodes that contain only one possible value
            for node in self.Nkeys:
                thisNode = self.vertList[node]
                if thisNode.value == 0:
                    
                    #create new array of powssible values this node can take, based on the starting board and function arguments
                    possibleValues = [i+1 for i in range(number_range)]

                    #examine neighboring nodes in row, col, sec, remove their values from possibe values
                    for groupKey in thisNode.connectionKeys:
                        for thisNeighbor in self.vertList[groupKey].connectionKeys:
                            neighborVal = self.vertList[thisNeighbor].value
                            if neighborVal != 0 and neighborVal in possibleValues:
                                possibleValues.remove(neighborVal)

                    #if a node with one possible value is found, add it to the output lists
                    if len(possibleValues) == 1:
                        thisNode.value = possibleValues[0]
                        thisNode.possible_values = []
                        nodeArrayOut.append(thisNode.id)
                        valueArrayOut.append(possibleValues[0])
                        self.numClues+=1

                        #repeat this method including the free clue in the search
                        continueChecking = True

                        if self.numClues == pow(number_range,2):
                            #The board has completed successfully
                            boardComplete = True

                        #reset the possible values based on the newly added value
                        self.getPossibleValues()
                    elif len(possibleValues) == 0:
                        #The values do not make up a valid board
                        boardCorrect = False


                    #temporarily update possible values for the node, which affects Process 2
                    else:
                        thisNode.possible_values = possibleValues

            if not boardComplete and boardCorrect:
                #Process 2: for each row, column, reigon, check if a solution value appears in only one node
                
                groupIdx = 0
                for groupKey in GroupKeys:
                    groupIdx += 1
                    thisGroup = self.vertList[groupKey]
                    valuePositions = [collections.OrderedDict() for i in range(number_range)] #one dictionary per solution value

                    for node in thisGroup.connectionKeys:
                        for value in self.vertList[node].possible_values:
                            valuePositions[value-1][self.vertList[node].id] = self.vertList[node]

                    #process dictionary list
                    for i in range(len(valuePositions)):
                        valDict = valuePositions[i]
                        #dicts will have no nodes if there is that given in a group, so if a dict has length 0, check if that value appears in the group
                        if len(valDict.keys()) == 1: #then there is only one cell in the group that contains this value
                            key,item = valDict.popitem()
                            if i+1 in item.possible_values and item.value == 0: #make sure the item can take this value, and is not a given
                                item.value = i + 1
                                item.possible_values = []
                                nodeArrayOut.append(key)
                                valueArrayOut.append(i + 1)
                                self.numClues+=1

                                #repeat this method including the free clue in the search
                                continueChecking = True

                                if self.numClues == pow(number_range,2):
                                    #The board has completed successfully
                                    boardComplete = True

                                #reset the possible values based on the newly added value
                                self.getPossibleValues()
                                # self.printPossibleValues()
                        elif len(valDict.keys()) == 0:
                            #differentiate between clue or error:
                            groupClues = []
                            for nkey in thisGroup.connectionKeys:
                                if self.vertList[nkey].value !=0:
                                    groupClues.append(self.vertList[nkey].value)

                            if i+1 not in groupClues:
                                #There is a solution value that does not appear anywhere in the group possibilities
                                boardCorrect = False
                                continueChecking = False

        #return list of possible values, or True if the board is complete and False if the board is invalid
        if not boardCorrect:
            #restore each node's starting value and possible_values
            for idx,nodeKey in enumerate(self.Nkeys):
                thisNode = self.vertList[nodeKey]
                thisNode.value = initial_values[idx]
                thisNode.possible_values = initial_posibilities[idx]

            #restore number of clues
            self.numClues = initial_numClues
            return False
        if boardComplete:
            print('Complete Board:')
            self.printBoard()
            return True
        else:
            #restore each node's starting value and possible_values
            for idx,nodeKey in enumerate(self.Nkeys):
                thisNode = self.vertList[nodeKey]
                thisNode.value = initial_values[idx]
                thisNode.possible_values = initial_posibilities[idx]

            #restore number of clues
            self.numClues = initial_numClues
            return (nodeArrayOut,valueArrayOut)

    def getFreeClues(self):
        #Call extrapolate() on the starting board to discover free clues (polynomial-time solutions from starting board) 
        #return True if the board is complete, False otherwise

        #extrapolate on the starting board
        freeClues = self.extrapolate([],[])

        if type(freeClues[0]) == bool:
            #The starting board is invaild
            if freeClues:
                print('------Solved Polynomial Board------')
                return True
            else:
                print('------Starting Board Invalid------')
                return False

        else:
            #The board contains a NP-time problem, freeClues is a tuple
            print('------Free Clues-------')
            for i in range(len(freeClues[0])): #Set the values of the nodes, and initialize their possibilities to []
                self.vertList[freeClues[0][i]].value = freeClues[1][i]
                self.vertList[freeClues[0][i]].possible_values = []
                self.numClues+=1
                print('Free Clues: ' + self.vertList[freeClues[0][i]].id + ' ' + str(freeClues[1][i]))
            print('resulting board:')
            self.printBoard()
            return False

    def printPossibleValues(self): #Print possible values
        for nodeKey in ['N'+str(i+1) for i in range(int(pow(number_range,2)))]:
            thisNode = self.vertList[nodeKey]
            if thisNode.value == 0:
                print(thisNode.id + ' ' +str(thisNode.possible_values))

    def GraphA(self):
        f = open('zzzz' + filename + 'workfile.txt', 'w')
        Bool = False
        Connections = []
        count = 0
        for nodeKey in ['N'+str(i+1) for i in range(int(pow(number_range,2)))]:
            thisNode = self.vertList[nodeKey]
            count += 1
            count2 = 0
            Bool2 = False
            if thisNode.value == 0:
                for nodeKey2 in ['N'+str(j+1) for j in range(int(pow(number_range,2)))]:
                    thisNode2 = self.vertList[nodeKey2]
                    count2 += 1
                    if nodeKey == nodeKey2:
                        nope = "nope"
                    elif thisNode2.value == 0:
                        for conkey in self.vertList[nodeKey].connectionKeys:
                            for conkey2 in self.vertList[nodeKey2].connectionKeys:
                                if conkey == conkey2:
                                    if Bool2 != True:
                                        Bool2 = True
                                        for value in thisNode.possible_values:
                                            if Bool == True:
                                                Bool = False
                                                break
                                            for value2 in thisNode2.possible_values:
                                                if Bool == False:
                                                    if value == value2:
                                                        Connections.append([count,count2])
                                                        Bool = True
                                                else:
                                                    break
            else:
                count2 += 1
        for item in Connections:
            for item2 in Connections:
                if item[0] == item2[1]:
                    if item[1] == item2[0]:
                        Connections.remove(item2)
        Edge_listy = []
        for item in Connections:
            for item2 in item:
                Edge_listy.append(item2)
        f.write(str(Edge_listy))

    def printBoardWith(self,nodeArrayIn,valueArrayIn):
        for i in range(len(nodeArrayIn)):
            self.vertList[nodeArrayIn[i]].value = valueArrayIn[i]
        self.printBoard()
        for i in range(len(nodeArrayIn)):
            self.vertList[nodeArrayIn[i]].value = 0

    def isConnected(self,NI,NJ):
        #pass in two node keys, return true if they share a group
        for i in range(3):
            if self.vertList[NI].connectionKeys[i] == self.vertList[NJ].connectionKeys[i]:
                return True
        return False

    def checkBoard(self,nodeArrayIn,valueArrayIn):
        #given starting boards and node, value pairs passed in, is the board correct?
        for i in range(len(nodeArrayIn)):
            self.vertList[nodeArrayIn[i]].value = valueArrayIn[i]
        for key in self.Rkeys + self.Ckeys + self.Skeys:
            allVals = [k + 1 for k in range(number_range)]
            for i in range(number_range):
                try:
                    allVals.remove(self.vertList[self.vertList[key].connectionKeys[i]].value)
                except ValueError:
                    return False
        return True

        for i in range(len(nodeArrayIn)):
            self.vertList[nodeArrayIn[i]].value = 0

    def DancingLinks(self,nodeArrayIn,valueArrayIn):
        #recursive method that performs a random depth-first search of the solution space

        if len(nodeArrayIn) + self.numClues == int(pow(number_range,2)):
            print()
            print('Final board:')
            print('Solution Valid?: ' + str(self.checkBoard(nodeArrayIn,valueArrayIn)))
            self.printBoardWith(nodeArrayIn,valueArrayIn)
            return True

        # #At this depth of the tree, choose one node to test next
        # Nkeys = ['N'+str(i+1) for i in range(int(pow(number_range,2)))] #build array here so we can also be destructive to it
        # for key in Nkeys:
        #     if self.vertList[key].value != 0 or key in nodeArrayIn: #reduce to possible nodes: nonclues, non specified
        #         Nkeys.remove(key)

        Nkeys = []
        for i in range(int(pow(number_range,2))):
            thisKey = 'N' + str(i+1)
            if thisKey not in nodeArrayIn and self.vertList[thisKey].value == 0:
                Nkeys.append(thisKey)

        #randomly select a node
        #Que = GenQue("DegreeQue.csv",Nkeys)
        levelNodeKey = random.choice(Nkeys)
        #levelNodeKey = Que.pop(0)
        levelNode = self.vertList[levelNodeKey]

        #generate possible values for a node based on the starting board, nodeArrayIn, valueArrayIn
        possibleValues = [i+1 for i in range(number_range)]

        #examine neighboring nodes in row, col, sec, remove their values from possibe values
        for groupKey in levelNode.connectionKeys:
            for thisNeighbor in self.vertList[groupKey].connectionKeys:
                neighborVal = self.vertList[thisNeighbor].value
                if neighborVal != 0 and neighborVal in possibleValues:
                    possibleValues.remove(neighborVal)

        #ALSO REMOVE POSSIBLE VALUES THAT COME IN THROUGH INPUT ARGUMENTS
        for i in range(len(nodeArrayIn)):
            if self.isConnected(levelNodeKey,nodeArrayIn[i]) and valueArrayIn[i] in possibleValues:
                possibleValues.remove(valueArrayIn[i])

        if possibleValues == []:
            #if possibleValues is empty, although it was not detected in extrapolate(), the board is invalid and the algorithm must backtrack
            return False

        #create a random permutations of the selected node's possible values
        valuePerm = random.sample(possibleValues,len(possibleValues))

        for value in valuePerm:
            #try each value, if the value works, call dancing links on all nodes that fall out of that value
            print('thisNode: ' + levelNode.id + ' thisValue: ' + str(value))
            exrNodes = nodeArrayIn[:] + [levelNode.id] #add ONLY this specific node and ID to this level's starting info
            exrValues = valueArrayIn[:] + [value]

            objOut = self.extrapolate(exrNodes,exrValues)

            if type(objOut) == bool:
                if objOut:
                    #the board is complete, let dancing links return True
                    return True
                #otherwise this board is incorrect, try next value at this level
            else:
                success = self.DancingLinks(objOut[0],objOut[1])
                if success:
                    #some child of this step is successful, return true
                    return True  
                #otherwise some child of this board is incorrect, we must restore 

###############################
#Run Code
###############################

path = "/Users/Ulrik/Desktop/NetworksProject/Sudoku_Boards/"

number_range = 9

Info = []
#start_time = time()

'''x = Multi_Graph('fourth.csv')
z = x.getVertex('N3')'''

county = 1 
for filename in os.listdir(path):
    if filename != ".DS_Store":
        if county <= 13:
            print(filename)
            start_time = time()
            x = Multi_Graph(filename)
            z = x.getVertex('N3')
            end_time = time()
            print("------Runtime: " + str(end_time - start_time) + ' seconds------')
            print("\n")
            Info.append(filename)
            Info.append(str(end_time - start_time))
            county += 1 

#print(Info)

'''start_time = time()

number_range = 9

x = Multi_Graph('sixth.csv')
z = x.getVertex('N3')

end_time = time()'''

# # extrapolate demo (comment in and run on 17clueboard.csv)
# exampleOut = list(x.extrapolate(['N77'],[6])) #run extrapolate on starting board plus the value 9 at node N77
# print()
# print('demo extrapolate: N77 is given the value 9')
# for clueInfo in exampleOut:
#     print(clueInfo[0] + ': ' + str(clueInfo[1]))

#problem: program tries to extrapolate on a free clue - also on values it already extrapolated on, overwriting its own process

#end_time = time()

#print("------Runtime: " + str(end_time - start_time) + ' seconds------')



