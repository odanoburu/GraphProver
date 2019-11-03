------------------------------------------------------------------------------
--  Main Module
--
--  This module defines ...
--
--  @author: Vitor, Marcela, Hermann, Jefferson, Bernardo
--
-------------------------------------------------------------------------------

require 'ConstantsForLove'
require 'ParseInput'
require 'Util/utility'
--require "Logic/NaturalDeduction/NaturalDeductionLogic"
--require "Logic/NaturalDeduction/NaturalDeductionAPI"
require "Logic/SequentCalculus/SequentCalculusLogic"
require "Logic/SequentCalculus/SequentCalculusAPI"
require 'logging.file'
require 'io'

-- Variáveis globais do modulo
local inspect = require "inspect"
local logger, font
local proofGraph, proofNode, nodeExpanding
local isDragging, isExpandingFormula
local FPSCAP = 60
local text, input_formula, input_command = ""
local editingState = NoInputing
local formulas
local total_kinetic_energy = 0

-- Private functions

--- Dada uma aresta, ele retorna o angulo em radianos que a aresta faz com o eixo horizontal.
-- É usada para escrever textos em cima das arestas.
local function getInclinacaoAresta(edge)
   local inclinacao
   local x2Maiorx1 = false
   local y2Maiory1 = false
   local invertSignal = 1 -- para saber para onde o angulo esta virado
   local x1, y1 = edge:getOrigem():getPosition()
   local x2, y2 = edge:getDestino():getPosition()

   local a,b,c

   -- Calculando o tamanho dos lados do triangulo retangulo que a aresta forma
   -- a = hipotenusa
   -- b e c catetos
   if x1 > x2 then
      b = x1 - x2
   elseif x2 > x1 then
      b = x2 - x1
      x2Maiorx1 = true
   else
      return math.rad(-90) -- A aresta esta na vertical
   end

   if y1 > y2 then
      c = y1 - y2
   elseif y2 > y1 then
      c = y2 - y1
      y2Maiory1 = true
   else
      return math.rad(0) -- A aresta esta na horizontal
   end

   -- Distancia entre 2 pontos
   a = math.pow(b,2) + math.pow(c,2)
   a = math.sqrt(a)

   -- Lei dos cossenos
   inclinacao = math.acos( (math.pow(a,2) + math.pow(b,2) - math.pow(c,2))/ (2*a*b) )

   -- Ajeitando a rotação para o lado correto
   if y2Maiory1 and x2Maiorx1 then
      invertSignal = 1
   elseif y2Maiory1 then
      invertSignal = -1
   elseif x2Maiorx1 then
      invertSignal = -1
   end

   return inclinacao * invertSignal
end

--- Um algoritmo massa-mola + carca eletrica aplicado ao grafo.
local function applyForces(graph)
   logger:debug("applyForces- Begin of applyForces function")

--   logger:debug("applyForces - total_kinetic_energy in the begin of the function: "..total_kinetic_energy)

   local nodes = graph:getNodes()
   local edges = graph:getEdges()

   for i=1, #nodes do
      nodes[i]:setInformation("Vx",0.0)
      nodes[i]:setInformation("Vy",0.0)
      nodes[i]:setInformation("m",0.5)
   end


   if total_kinetic_energy < 100 then
      total_kinetic_energy = 0
      return
   end


--   repeat
--      total_kinetic_energy = 0

      for i=1, #nodes do

         local Fx = 0.0
         local Fy = 0.0
         local Vx = 0.0
         local Vy = 0.0

         nodes[i]:setInformation("Fx",Fx)
         nodes[i]:setInformation("Fy",Fy)
         for j=1, #nodes do
            if i ~= j then
               dx = nodes[i]:getPositionX() - nodes[j]:getPositionX()
               dy = nodes[i]:getPositionY() - nodes[j]:getPositionY()
               rsq = (dx*dx) + (dy*dy)

               Fx = nodes[i]:getInformation("Fx")+(100*dx/rsq)
               nodes[i]:setInformation("Fx",Fx)

               Fy = nodes[i]:getInformation("Fy")+(100*dy/rsq)
               nodes[i]:setInformation("Fy",Fy)
            end
         end

         for j=1, #edges do
            local edge = edges[j]
            local nodeO = edge:getOrigem()
            local nodeD = edge:getDestino()

            if nodeO:getLabel() == nodes[i]:getLabel() or nodeD:getLabel() == nodes[i]:getLabel() then
               local Xi=0
               local Xj=0
               local Yi=0
               local Yj=0
               if nodeO:getLabel() == nodes[i]:getLabel() then
                  Xi,Yi = nodeO:getPosition()
                  Xj,Yj = nodeD:getPosition()
               else
                  Xi,Yi = nodeD:getPosition()
                  Xj,Yj = nodeO:getPosition()
               end

               dx = Xj - Xi
               dy = Yj - Yi

               Fx = nodes[i]:getInformation("Fx")+(0.06*dx)
               nodes[i]:setInformation("Fx", Fx)

               Fy = nodes[i]:getInformation("Fy")+(0.06*dy)
               nodes[i]:setInformation("Fy", Fy)
            end
         end

         Vx = nodes[i]:getInformation("Vx")+(nodes[i]:getInformation("Fx")*0.85)
         Vy = nodes[i]:getInformation("Vy")+(nodes[i]:getInformation("Fy")*0.85)

         nodes[i]:setInformation("Vx", Vx)
         nodes[i]:setPositionX(nodes[i]:getPositionX()+nodes[i]:getInformation("Vx"))
         nodes[i]:setInformation("Vy", Vy)
         nodes[i]:setPositionY(nodes[i]:getPositionY()+nodes[i]:getInformation("Vy"))
         total_kinetic_energy = total_kinetic_energy + (nodes[i]:getInformation("m") * ((nodes[i]:getInformation("Vx")^2) + (nodes[i]:getInformation("Vy")^2)))

         logger:debug("applyForces - Fx: "..nodes[i]:getInformation("Fx"))
         logger:debug("applyForces - Fy: "..nodes[i]:getInformation("Fy"))
         logger:debug("applyForces - Vx: "..nodes[i]:getInformation("Vx"))
         logger:debug("applyForces - Vy: "..nodes[i]:getInformation("Vy"))
         logger:debug("applyForces -  m: "..nodes[i]:getInformation("m"))
         logger:debug("applyForces - Vx^2: "..nodes[i]:getInformation("Vx")^2)
         logger:debug("applyForces - Vy^2: "..nodes[i]:getInformation("Vy")^2)
         logger:debug("applyForces - total_kinetic_energy (m * (Vx^2 + Vy^2)): "..total_kinetic_energy)

         if total_kinetic_energy < 100 or total_kinetic_energy > 80000000 then
            total_kinetic_energy = 0
            logger:debug("applyForces - total_kinetic_energy < 100")
            break
         end

      end
--   until total_kinetic_energy < 50000
end

--- Ela prepara as posições (x,y) de todos os vertices para que eles possam ser desenhados.
local function prepareGraphToDraw(graph)

   nodes = graph:getNodes()

   posX = xBegin
   posY = yBegin

   if nodes ~= nil then
      for  i = 1, #nodes do
         if nodes[i]:getPosition() == nil then -- só atualiza os nós que nao tem posicao.
            nodes[i]:setPosition(posX,posY)
            if i % 2 == 0 then
               posX = posX + 10
            else
               posY = posY + 10
            end
         end
      end
   end


   total_kinetic_energy = 101
   return graph
end

--- Receive a graph and draws it on the screen.
local function drawGraphEvent(graph)
   local i = 1

   assert( getmetatable(graph) == Graph_Metatable , "drawGraphEvent expects a graph.")

   local nodes = graph:getNodes()
   local edges = graph:getEdges()

   -- Desenha os vertices
   if nodes ~= nil then
      while i <= #nodes do

         local node = nodes[i]

         if isExpandingFormula then
           if node:getInformation("isSelected") == true then
              love.graphics.setColor(255, 255, 0) -- Yellow circle
           end
         else
           if node:getInformation("isProved") == nil then
              love.graphics.setColor(204, 204, 204) -- Gray circle
           elseif node:getInformation("isProved") == false then
              love.graphics.setColor(255, 0, 0) -- Red circle
           elseif node:getInformation("isProved") == true then
              love.graphics.setColor(0, 0, 255) -- Blue circle
           end
           node:setInformation("isSelected", false)
         end

         if node:getInformation("found") == true then
            love.graphics.setColor(255, 255, 0) -- Yellow circle
         end

         if node:getPositionX() ~= nil then
            love.graphics.circle("fill", node:getPositionX(), node:getPositionY(), raioDoVertice, 25)
            love.graphics.setColor(0, 0, 0, 99) -- Black 99%
            love.graphics.circle("line", node:getPositionX(), node:getPositionY(), 6)
            love.graphics.print(node:getLabel(), node:getPositionX() - 10, node:getPositionY() - circleSeparation , 0, escalaLetraVertice, escalaLetraVertice )
         end

         i = i + 1
      end
   end

   i=1
   -- Desenha as arestas
   if edges ~= nil then
      while i <= #edges do

         local edge = edges[i]

         love.graphics.setColor(0, 0, 0, 99) -- Black 99%
         local x1, y1 = edge:getOrigem():getPosition()
         local x2, y2 = edge:getDestino():getPosition()
         love.graphics.line(x1, y1, x2, y2)

         if x1 ~= nil and y1 ~= nil and x2 ~= nil and y2 ~= nil then
            inclinacao = getInclinacaoAresta(edge)
            love.graphics.print(edge:getLabel(), (x1 + x2)/2 , (y1 + y2)/2  , inclinacao, escalaLetraAresta, escalaLetraAresta )
         end

         i = i + 1
      end
   end

   -- applyForces(graph)
end

--- Esta função verifica se algum vertice foi clicado pelo usuário e retorna este vertice.
local function getNodeClicked()
   -- Varrer todo o grafo procurando o vertice que pode ter sido clicado.
   nodes = proofGraph:getNodes()
   for i=1, #nodes do
      x,y = nodes[i]:getPosition()

      if (love.mouse.getX() <= x + raioDoVertice) and (love.mouse.getX() >= x - raioDoVertice) then
         if (love.mouse.getY() <= y + raioDoVertice) and (love.mouse.getY() >= y - raioDoVertice) then
            -- Este vertice foi clicado
            nodes[i]:setInformation("isSelected", true)
            return nodes[i]
         end
      end
   end
   return nil
end

-- Event actions functions

local function proofStarted()
   local ret = false
   if (proofGraph ~= nil) then
      if (proofGraph:getNode(lblNodeGG) ~= nil) then
         if (proofGraph:getNode(lblNodeGG):getEdgesOut() ~= nil) and
            (#proofGraph:getNode(lblNodeGG):getEdgesOut() ~= 0) then
            ret = true
         end
      end
   end
   return ret
end

local function expandAll()
   logger:debug("expandAll - Begin of expandAll function")
   if proofStarted() then
      local graph = LogicModule.expandAll(proofGraph)
      proofGraph = prepareGraphToDraw(graph)
   end
end

local function inputFormula()
   logger:debug("inputFormula - Begin of inputFormula function")
   editingState = InputingFormula

   text = "Type your formula or choose an example below: "
   input_formula = ""

   proofGraph = LogicModule.createGraphFromTable("empty")
   prepareGraphToDraw(proofGraph)
end

local function runInput()
   local parsed_formula = parse_input(input_formula)
   t_formula = convert_formula_totable(parsed_formula)

   local t_mimp_formula = implicational(t_formula)
   logger:info("inputFormula - alpha: "..convert_formula_tostring(t_mimp_formula))

   proofGraph = LogicModule.createGraphFromTable(t_mimp_formula)
   prepareGraphToDraw(proofGraph)
end

local function inputCommand()
   editingState = InputingCommand

   text = "Type your command: "
   input_command = ""
end

local function runCommand()
   input_command = input_command:gsub("%(", "%(\"")
   input_command = input_command:gsub("%)", "\"%)")
   input_command = input_command:gsub(",", "\",\"")
   input_command = input_command:gsub(",\" ", ",\"")

   loadstring(input_command)()
   proofGraph = LogicModule.getGraph()
   prepareGraphToDraw(proofGraph)
   inputCommand()
end

local function expandFormula()
   if proofStarted() then
      if (nodeExpanding ~= nil) then
         local ret, graph = LogicModule.expandNode(proofGraph, proofNode, nodeExpanding)
         proofGraph = prepareGraphToDraw(graph)
      end
   end
end

local function printProof()
   if proofStarted() then
      ret = PrintModule.printProof(proofGraph)

      if ret then
         os.showProof()
      end
   end
end

local function printGraph()
   if proofStarted() then
      PrintModule.printGraph(proofGraph)
      os.showGraph()
   end
end

-- Events functions

local function showInputTextEvent()
   -- Mudança necessária para Löve 0.10. Sem ela, o fundo ficava preto
   love.graphics.clear(love.graphics.getBackgroundColor())
   font = love.graphics.newFont(12)

   love.graphics.setColor(0, 0, 255)
   love.graphics.setFont(font)
   love.graphics.printf(text, 0, 0, love.graphics.getWidth())

   local y = 200
   local i = 1
   formulas = {}
   function Formula(f)
      formulas[i] = f[2]
      love.graphics.printf(i..") "..f[1].." "..f[2], 0, y + 30, love.graphics.getWidth())
      y = y + 30
      i = i + 1
   end

   --dofile("Test/data")
   assert(love.filesystem.load("Test/data"))()
end

local function expandAllButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 5
   local xLen = 55
   local yLen = 40

   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      if love.mouse.isDown(leftMouseButton) then
         expandAll()
         love.timer.sleep(buttonTime)
      end
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.printf({{0, 0, 0}, expandAllButtonName}, xPos, yPos + 5, xLen, "center")
end

local function inputFormulaButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 50
   local xLen = 55
   local yLen = 40

   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      if love.mouse.isDown(leftMouseButton) then
         inputFormula()
         love.timer.sleep(buttonTime)
      end
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.printf({{0, 0, 0}, inputFormulaButtonName}, xPos, yPos + 5, xLen, "center")
end

local function expandFormulaButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 95
   local xLen = 55
   local yLen = 40

   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      if love.mouse.isDown(leftMouseButton) then
         -- TODO remover a referência a focus?
         isChoosingFocus = true
         love.timer.sleep(buttonTime*2)
      end
      love.timer.sleep(buttonTime*2)
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.printf({{0, 0, 0}, expandFormulaButtonName}, xPos, yPos + 5, xLen, "center")
end

local function printProofButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 140
   local xLen = 55
   local yLen = 40
   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      if love.mouse.isDown(leftMouseButton) then
         printProof()
         love.timer.sleep(buttonTime)
      end
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.printf({{0, 0, 0}, printProofButtonName}, xPos, yPos + 5, xLen, "center")
end

local function printGraphButtonEvent()
   local xPos = windowWidth - 60
   local yPos = 185
   local xLen = 55
   local yLen = 40
   if love.mouse.getX() >= xPos and love.mouse.getX() <= xPos + xLen and love.mouse.getY() >= yPos and love.mouse.getY() <= yPos + yLen then
      if love.mouse.isDown(leftMouseButton) then
         printGraph()
         love.timer.sleep(buttonTime)
      end
      love.graphics.setColor(100, 100, 200)
   else
      love.graphics.setColor(0, 100, 200)
   end
   love.graphics.rectangle("fill", xPos, yPos, xLen, yLen)
   love.graphics.setColor(0, 0, 255)
   love.graphics.setLineStyle("smooth")
   love.graphics.line(xPos, yPos, xPos, yPos + yLen)
   love.graphics.line(xPos, yPos + yLen, xPos + xLen, yPos + yLen)
   love.graphics.setColor(255, 255, 255)
   love.graphics.line(xPos + xLen, yPos, xPos + xLen, yPos + yLen)
   love.graphics.line(xPos, yPos, xPos + xLen, yPos)
   love.graphics.printf({{0, 0, 0}, printGraphButtonName}, xPos, yPos + 5, xLen, "center")
end

--- Esta função é chamada pela love.draw.
-- A todo instante ela verifica se o botão esquerdo do mouse foi apertado. Em caso positivo
-- conforme o botão continuar sendo pressionado e caso o clique tenha sido em um vertice esta função:
-- 1- Ira alterar a posição de desenho do vertice, criando o efeito do drag and drop, ou;
-- 2- Ira mover o screen todo, ou ;
-- 3- Ira indicar um Sequent como foco (se isExpandingFormula for verdadeiro) , ou;
-- 4- Ira chamar a funcao que expande o noh (segundo o calculo lohgico implementado), se
-- o foco (no do tipo Sequent) estiver definido.
local function dragNodeOrScreenOrSelectFocusEvent()

   -- TODO remover a parte do focus?
   if love.mouse.isDown(leftMouseButton) and isChoosingFocus then

      proofNode = getNodeClicked()

      if proofNode then
         isExpandingFormula = true
         love.timer.sleep(2*buttonTime)
      end

   elseif love.mouse.isDown(leftMouseButton) and isExpandingFormula then

      nodeExpanding = getNodeClicked()

      if nodeExpanding then
         isExpandingFormula = false
         expandFormula()
      end

   end

   if love.mouse.isDown(leftMouseButton) and not isDragging then

      nodeMoving = getNodeClicked()
      isDragging = true

      xInitial = love.mouse.getX()
      yInitial = love.mouse.getY()
      -- Mudar o xInicial e o yInicial sempre que o mouse parar tb seria uma boa!

      -- Vericia se o usuário quer arrastar a tela
   elseif not love.mouse.isDown(leftMouseButton) then
      isDragging = false
      nodeMoving = "nao vazio"

      -- Usuario arrastando um vertice
   elseif nodeMoving ~= "nao vazio" and nodeMoving ~= nil then
      nodeMoving:setPosition(love.mouse.getX(), love.mouse.getY())
      -- applyForces(proofGraph)

    -- Usuario arrastando toda a tela
   elseif nodeMoving == nil then
      nodes = proofGraph:getNodes()
      for i=1, #nodes do
         x,y = nodes[i]:getPosition()
         deslocamentoX = math.abs(love.mouse.getX() - xInitial)/10
         deslocamentoY = math.abs(love.mouse.getY() - yInitial)/10

         if love.mouse.getX() < xInitial then
            x = x - 5
         elseif love.mouse.getX() > xInitial then
            x = x + 5
         end

         if love.mouse.getY() < yInitial then
            y = y - 5
         elseif love.mouse.getY() > yInitial then
            y = y + 5
         end

         nodes[i]:setPosition(x, y)
      end
   end
end

-- Public functions: Love events
function love.resize(w, h)
   windowWidth = w
   windowHeight = h
end

function love.keypressed(key)
   if key == "a" and love.keyboard.isDown("lctrl") then
      expandAll()
   elseif key == "i" and love.keyboard.isDown("lctrl") then
      inputFormula()
   elseif key == "p" and love.keyboard.isDown("lctrl") then
      printProof()
   elseif key == "g" and love.keyboard.isDown("lctrl") then
      printGraph()
   elseif key == "t" and love.keyboard.isDown("lctrl") then
      inputCommand()
   end

   if editingState == InputingFormula then
      if key == "backspace" then
         input_formula = input_formula:sub(1, input_formula:len()-1)
         text = "Type your formula or choose an example below: " .. input_formula
      end

      if key == "return" or key == "kpenter" then
         if tonumber(input_formula) then
            input_formula = formulas[tonumber(input_formula)]
         end

         if input_formula ~= "" then
            local status, err = pcall(runInput)
            if not status then
               input_formula = err
               text = "Type your formula or choose an example below: " .. input_formula
            end
         end
      end
   end

   if editingState == InputingCommand then
      if key == "backspace" then
         input_command = input_command:sub(1, input_command:len()-1)
         text = "Type your command: " .. input_command
      end

      if key == "return" or key == "kpenter" then
         local status, err = pcall(runCommand)
         if not status then
            input_command = err
            text = "Type your command: " .. input_command
         end
      end
   end
end

function love.textinput(t)
   if editingState == InputingFormula then
      input_formula = input_formula .. t
      text = "Type your formula or choose an example below: " .. input_formula
   elseif editingState == InputingCommand then
      input_command = input_command .. t
      text = "Type your command: " .. input_command
   end
end

function love.load(arg)
   -- Prepare to debug with ZeroBrane
   if arg[#arg] == "-debug" then
      require("mobdebug").start()
   end

   -- Log control
   logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
   logger:setLevel(logging.DEBUG)

   -- Love initial configuration
   love.graphics.setBackgroundColor(255, 255, 255) -- White Color
   love.graphics.setColor(0, 0, 0) -- Black Color
   font = love.graphics.newFont(11)
   isDragging = false

   -- TODO remover a referência a focus?
   isChoosingFocus = false
   isExpandingFormula = false

   -- Initialize the proof graph
   inputFormula()
end

function love.draw()
   showInputTextEvent()
   expandAllButtonEvent()
   inputFormulaButtonEvent()
   expandFormulaButtonEvent()
   printProofButtonEvent()
   printGraphButtonEvent()
   drawGraphEvent(proofGraph)
   dragNodeOrScreenOrSelectFocusEvent()
end
