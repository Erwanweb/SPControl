"""
Swimming pool full control with Analyzer
Author: Ronelabs Team,
Version:    0.0.1: alpha
            0.0.2: beta
            0.1.1: test
"""
"""

<plugin key="SPControl" name="ZZ - Swimming Pool Control with analyzer" author="Ronelabs Team" version="0.1.1" externallink="https://github.com/Erwanweb/SPControl">
    <description>
        <h2>Swimming Pool Full Control</h2><br/>
        Easily implement in Domoticz an full control of Swimming Pool by using a floating water analyzer<br/>
        <h3>Set-up and Configuration</h3>
    </description>
    <params>
        <param field="Username" label="Treatment type" width="300px">
            <options>
                <option label="Chlorine" value="1"  default="true"/>
                <option label="Bromine" value="1"/>
                <option label="Salt" value="2"/>
            </options>
        </param>
        <param field="Password" label="filtration power" width="300px">
            <options>
                <option label="Overpowered +++" value="0.6"/>
                <option label="Overpowered ++" value="0.7"/>
                <option label="Overpowered" value="0.8"/>
                <option label="Normal" value="1"  default="true"/>
                <option label="Underpowered" value="1.2"/>
                <option label="Underpowered ++" value="1.3"/>
                <option label="Underpowered +++" value="1.4"/>
            </options>
        </param>
        <param field="Mode1" label="Analyzer (0 for not): PH, Redox (csv list of idx)" width="200px" required="true" default=""/>
        <param field="Mode3" label="Actuators (0 for not): Filtration, Heater (csv list of idx)" width="100px" required="true" default=""/>
        <param field="Mode4" label="Permament Water Temp. Sensors (csv list of idx)" width="100px" required="true" default=""/>
        <param field="Mode5" label="In Flow Water Temp. Sensors (csv list of idx)" width="100px" required="flase" default=""/>
        <param field="Mode6" label="Logging Level" width="200px">
            <options>
                <option label="Normal" value="Normal"  default="true"/>
                <option label="Verbose" value="Verbose"/>
                <option label="Debug - Python Only" value="2"/>
                <option label="Debug - Basic" value="62"/>
                <option label="Debug - Basic+Messages" value="126"/>
                <option label="Debug - Connections Only" value="16"/>
                <option label="Debug - Connections+Queue" value="144"/>
                <option label="Debug - All" value="-1"/>
            </options>
        </param>
    </params>
</plugin>
"""

import Domoticz
import sys
from base64 import b64encode
import base64
import json
from urllib.parse import quote
import urllib.parse as parse
import urllib.request as request
import itertools
import re
from datetime import datetime, timedelta, time
import time
import math
import html
import requests
import os
import subprocess as sp
from distutils.version import LooseVersion


class deviceparam:

    def __init__(self, unit, nvalue, svalue):
        self.unit = unit
        self.nvalue = nvalue
        self.svalue = svalue
        self.debug = False

class BasePlugin:
        
    def __init__(self):
        self.lastDateTime = None
        self.isStarted = False
        # default values of the Flipr
        self.PHVal = 7.2
        self.PHText = "Parfait"
        self.RedoxVal = 600
        self.RedoxText = "Parfait"
        self.SPTemp = 25
        self.SPTempCheck = 25
        self.OppSPTempSens = False
        self.nexttemps = datetime.now()
        self.nextAnalyzer = datetime.now()
        self.PHValNet = 7
        self.RedoxValNet = 600
        self.FiltrationVarNextRefresh = datetime.now()
        self.PumpTemp = 12
        self.PLUGINstarteddtime = datetime.now()
        self.SunAtSouthHour = 14
        self.SunAtSouthMin = 0
        self.SunAtSouth = datetime.now()
        self.startpump = datetime.now()
        self.stoppump = datetime.now()
        self.Daily = datetime.now()
        self.pumpon = False
        self.Heating = False
        self.pumpidx = 0
        self.pumporderchangedtime = datetime.now()
        self.pumponstarttime = datetime.now()
        self.setpoint = 28
        self.heateridx = 0
        self.heaterorderchangedtime = datetime.now()
        self.PHValidx = 0
        self.RedoxValidx = 0
        self.TempSensors = []
        self.TempSensorsOpp = []
        self.pumppower = 1
        return

    def onStart(self):

        # setup the appropriate logging level
        try:
            debuglevel = int(Parameters["Mode6"])
        except ValueError:
            debuglevel = 0
            self.loglevel = Parameters["Mode6"]
        if debuglevel != 0:
            self.debug = True
            Domoticz.Debugging(debuglevel)
            DumpConfigToLog()
            self.loglevel = "Verbose"
        else:
            self.debug = False
            Domoticz.Debugging(0)


        # create the child devices if these do not exist yet
        devicecreated = []
        if 1 not in Devices:
            Options = {"LevelActions": "||", "LevelNames": "Off|Auto|Forced", "LevelOffHidden": "false", "SelectorStyle": "0"}
            Domoticz.Device(Name="Filtration control", Unit=1, TypeName="Selector Switch", Switchtype=18, Image=9, Options=Options, Used=1).Create()
            devicecreated.append(deviceparam(1, 0, "0"))  # default is Off state
        if 2 not in Devices:
            Options = {"LevelActions": "||", "LevelNames": "Off|Auto|Forced", "LevelOffHidden": "false", "SelectorStyle": "0"}
            Domoticz.Device(Name="Heating control", Unit=2, TypeName="Selector Switch", Switchtype=18, Image=15, Options=Options, Used=1).Create()
            devicecreated.append(deviceparam(2, 0, "0"))  # default is Off state
        if 3 not in Devices:
            Domoticz.Device(Name="Filtration", Unit=3, TypeName="Switch", Image=9, Used=1).Create()
            devicecreated.append(deviceparam(3, 0, ""))  # default is Off
        if 4 not in Devices:
            Domoticz.Device(Name="Water temp", Unit=4, TypeName="Temperature", Used=1).Create()
            devicecreated.append(deviceparam(4, 0, "20"))  # default is 20 degrees
        if 5 not in Devices:
            Domoticz.Device(Name="Setpoint", Unit=5, Type=242, Subtype=1, Used=1).Create()
            devicecreated.append(deviceparam(5, 0, "28"))  # default is 28 degrees
        if 6 not in Devices:
            Domoticz.Device(Name="Heating request", Unit=6, TypeName="Switch", Image=9).Create()
            devicecreated.append(deviceparam(6, 0, ""))  # default is Off
        if 7 not in Devices:
            Domoticz.Device(Name="PH", Unit=7, TypeName="Alert", Used=1).Create()
            devicecreated.append(deviceparam(7, 0, "waiting for value"))  # default is clear
        if 8 not in Devices:
            Domoticz.Device(Name="PH Value", Unit=8, Type=243, Subtype=31, Used=1).Create()
            devicecreated.append(deviceparam(8, 0, ""))  # default is 0
        if 9 not in Devices:
            Domoticz.Device(Name="Redox", Unit=9, TypeName="Alert", Used=1).Create()
            devicecreated.append(deviceparam(9, 0, "waiting for value"))  # default is clear
        if 10 not in Devices:
            Domoticz.Device(Name="Redox Value", Unit=10, Type=243, Subtype=31, Used=1).Create()
            devicecreated.append(deviceparam(10, 0, ""))  # default is 0
        if 11 not in Devices:
            Domoticz.Device(Name="Info", Unit=11, Type=243, Subtype=19, Used=1).Create()
            devicecreated.append(deviceparam(11, 0, "waiting for value"))  # default is clear

        # if any device has been created in onStart(), now is time to update its defaults
        for device in devicecreated:
            Devices[device.unit].Update(nValue=device.nvalue, sValue=device.svalue)

        # splits parameters
        self.pumppower = float(Parameters["Password"])

        # splits additional parameters
        # analyzer
        params1 = parseCSV(Parameters["Mode1"])
        if len(params1) == 2:
            self.PHValidx = CheckParam("PH", params1[0], 0)
            self.RedoxValidx = CheckParam("Redox", params1[1], 0)
        else:
            Domoticz.Error("Error reading Mode1 parameters")
        # pump and heater
        params3 = parseCSV(Parameters["Mode3"])
        if len(params3) == 2:
            self.pumpidx = CheckParam("Filtration", params3[0], 0)
            self.heateridx = CheckParam("Heater", params3[1], 0)
        else:
            Domoticz.Error("Error reading Mode3 parameters")

        # build lists of sensors
        params4 = parseCSV(Parameters["Mode4"])
        if len(params4) > 0:
            self.TempSensors = parseCSV(Parameters["Mode4"])
            Domoticz.Debug("Permanent Temperature sensors = {}".format(self.TempSensors))
        else:
            Domoticz.Error("Error reading Mode4 parameters")

        params5 = parseCSV(Parameters["Mode5"])
        if len(params5) > 0 :
            self.OppSPTempSens = True
            self.TempSensorsOpp = parseCSV(Parameters["Mode5"])
            Domoticz.Debug("Additional Temperature sensors = {}".format(self.TempSensorsOpp))

        # updating temp, timers and filtration
        now = datetime.now()
        self.readTemps()
        Devices[3].Update(nValue=0, sValue=Devices[3].sValue)
        #self.readTemps = now - timedelta(hours=36)
        self.FiltrationVarNextRefresh = now - timedelta(hours=36)
        self.pumporderchangedtime = now - timedelta(hours=36)

        # Check if the used control mode is ok
        if (Devices[1].sValue == "10"):
            self.powerOn = 1
            self.forced = 0

        elif (Devices[1].sValue == "20"):
            self.powerOn = 1
            self.forced = 1

        elif (Devices[1].sValue == "0"):
            self.powerOn = 0
            self.forced = 0

        # Set domoticz heartbeat to 20 s (onheattbeat() will be called every 20 )
        Domoticz.Heartbeat(20)

        # Now we can enabling the plugin
        self.isStarted = True

# Plugin STOP  ---------------------------------------------------------

    def onStop(self):
        Domoticz.Debug("onStop called")
        # prevent error messages during disabling plugin
        self.isStarted = False

# DZ Widget actions  ---------------------------------------------------

    def onCommand(self, Unit, Command, Level, Color):

        Domoticz.Debug("onCommand called for Unit {}: Command '{}', Level: {}".format(Unit, Command, Level))

        if (Unit == 1):
            Devices[1].Update(nValue=self.powerOn, sValue=str(Level))
            if (Devices[1].sValue == "10"):  # Mode auto
                self.powerOn = 1
                self.forced = 0
                Devices[1].Update(nValue=1, sValue=Devices[1].sValue)
            elif (Devices[1].sValue == "20"):  # Manual Mode
                self.powerOn = 1
                self.forced = 1
                Devices[1].Update(nValue=1, sValue=Devices[1].sValue)
            else : # Off
                Devices[1].Update(nValue=0, sValue=Devices[1].sValue)
                self.powerOn = 0
                self.forced = 0
                Devices[2].Update(nValue=self.powerOn, sValue=Devices[2].sValue)
            # Update child devices
            if not (Devices[2].sValue == "0"):  # Heating Off
                Devices[2].Update(nValue=self.powerOn, sValue=Devices[2].sValue)

        if (Unit == 2):  # Heating
            Devices[2].Update(nValue=self.powerOn, sValue=str(Level))
            if (Devices[2].sValue == "0"):  # Off
                Devices[2].Update(nValue=0, sValue=Devices[2].sValue)
            else :
                Devices[2].Update(nValue=self.powerOn, sValue=str(Level))

        if (Unit == 5):  # Setpoint
            Devices[5].Update(nValue=self.powerOn, sValue=str(Level))
            self.setpoint = round(float(Devices[5].sValue))

        self.onHeartbeat()


# Heartbeat  ---------------------------------------------------

    def onHeartbeat(self):

        Domoticz.Debug("onHeartbeat called")
        now = datetime.now()

        # Regul-regul --------------------------------------------------
        if not Devices[1].sValue == "0":  # Off
            if Devices[1].sValue == "10":  # auto
                self.powerOn = 1
                self.forced = 0
            if Devices[1].sValue == "20":  # forced
                self.powerOn = 1
                self.forced = 1
        else :
            self.powerOn = 0
            self.forced = 0

        # Check Temp ---------------------------------------------------

        if self.nexttemps + timedelta(minutes=2) <= now:
            self.readTemps()

        self.SPTempCheck = round(float(self.SPTemp))

        # Check Analyzer------------------------------------------------

        if self.nextAnalyzer + timedelta(minutes=5) <= now:
            self.readAnalyzer()

        # Filtration ---------------------------------------------------
        # Check mode and set all good
        if Devices[1].sValue == "0": # Off
            self.forced = 0
            self.pumpon = False
            if Devices[3].nValue == 1:
                Devices[3].Update(nValue=0, sValue=Devices[3].sValue)
                DomoticzAPI("type=command&param=switchlight&idx={}&switchcmd=Off".format(self.pumpidx))
                self.pumporderchangedtime = datetime.now()
            Domoticz.Debug("System is OFF - ALL OFF")
            Devices[11].Update(nValue=0, sValue="OFF")
        elif Devices[1].sValue == "20": # Manual
            self.forced = 1
            if Devices[3].nValue == 0:
                Devices[3].Update(nValue=1, sValue=Devices[3].sValue)
                DomoticzAPI("type=command&param=switchlight&idx={}&switchcmd=On".format(self.pumpidx))
                self.pumporderchangedtime = datetime.now()
                self.pumponstarttime = datetime.now()
            Domoticz.Debug("System is ON - Filtration in MANUAL Mode")
            Devices[11].Update(nValue=0, sValue="ON - Manual Mode")
        else : # Auto
            Domoticz.Debug("System is ON - Filtration in AUTO Mode")
            self.forced = 0
            # If Auto :
            now = datetime.now()
            # We check time needed for filtration, every 15 minutes
            if self.FiltrationVarNextRefresh <= now:
                #self.FiltrationVarNextRefresh = now + timedelta(minutes=30)
                if self.SPTempCheck >= 31:
                    self.PumpTemp = 24
                    self.FiltrationVarNextRefresh = now + timedelta(hours=12)
                    Domoticz.Debug("Filtration is all the time because of high SP Temp at : " + str(self.SPTemp))
                    #Devices[16].Update(nValue=0, sValue="Auto - Calc. 24h/24")
                    #Devices[16].Update(nValue=0, sValue="Auto - "+ str(self.SPTemp))
                else :
                    if self.SPTempCheck <= 15:
                        if self.SPTempCheck <= 10:
                            self.PumpTemp = 2
                            self.FiltrationVarNextRefresh = now + timedelta(hours=2)
                            Domoticz.Debug("Filtration is fixed at 2h per day because SP Temp lower than 10 and exactly at : " + str(self.SPTemp))
                            #Devices[16].Update(nValue=0, sValue="Auto - Calc. 2h")
                        else :
                            self.SPTempCheck = 3
                            self.FiltrationVarNextRefresh = now + timedelta(hours=2)
                            Domoticz.Debug("Filtration is fixed at 3h per day because low SP Temp between 10 and 15, and exactly at : " + str(self.SPTemp))
                            #Devices[16].Update(nValue=0, sValue="Auto - Calc. 3h")
                    else :
                        if self.SPTempCheck <= 24:
                            self.PumpTemp = round((self.SPTempCheck / 3) * self.pumppower, 1)
                            self.FiltrationVarNextRefresh = now + timedelta(hours=4)
                            Domoticz.Debug("Filtration calcul. dur. is 1/3 of SP Temp and so fixed at (h): " + str(self.PumpTemp))
                            #Devices[16].Update(nValue=0, sValue="Auto - Calc. 3h")
                        else:
                            self.PumpTemp = round((self.SPTempCheck / 2) * self.pumppower, 1)
                            self.FiltrationVarNextRefresh = now + timedelta(hours=4)
                            Domoticz.Debug("Filtration calcul. dur. is 1/2 of SP Temp and so fixed at (h): " + str(self.PumpTemp))
                # Now we set timers
                jsonData = DomoticzAPI("type=command&param=getSunRiseSet")
                if jsonData :
                # datetime(year, month, day, hour, minute, second, microsecond)
                    SunAtSouthHour = int(jsonData['SunAtSouth'].split(':')[0])
                    SunAtSouthMin = int(jsonData['SunAtSouth'].split(':')[1])
                    now = datetime.now()
                    self.SunAtSouth = datetime(year=now.year, month=now.month, day=now.day, hour=SunAtSouthHour, minute=SunAtSouthMin, second=0, microsecond=0)
                    Domoticz.Debug("Sun at south at : " + str(self.SunAtSouth))
                    self.startpump = self.SunAtSouth - timedelta(hours=(self.PumpTemp/ 2))
                    Domoticz.Debug("Pump ON timer fixed at : " + str(self.startpump))
                    self.stoppump = self.startpump + timedelta(hours=(self.PumpTemp))
                    Domoticz.Debug("Pump OFF timer fixed at : " + str(self.stoppump))
                else : # timers by default
                    now = datetime.now()
                    self.SunAtSouth = datetime(year=now.year, month=now.month, day=now.day, hour=14, minute=0, second=0, microsecond=0)
                    self.startpump = self.SunAtSouth - timedelta(hours=(self.PumpTemp / 2))
                    Domoticz.Debug("Pump ON timer default value at : " + str(self.startpump))
                    self.stoppump = self.startpump + timedelta(hours=(self.PumpTemp))
                    Domoticz.Debug("Pump OFF timer default value at : " + str(self.stoppump))
            # And now, we check state and turn on or off the pump
            now = datetime.now()
            if self.startpump < now and self.stoppump > now : # We are in the period of filtration
                self.pumpon = True
                if Devices[3].nValue == 0:
                    Devices[3].Update(nValue=1, sValue=Devices[3].sValue)
                    DomoticzAPI("type=command&param=switchlight&idx={}&switchcmd=On".format(self.pumpidx))
                    self.pumporderchangedtime = datetime.now()
                    self.pumponstarttime = datetime.now()
                Domoticz.Debug("Pump is ON since "+ str(self.startpump))
                Domoticz.Debug("Filtration calcul. dur. is : " + str(self.PumpTemp))
                Domoticz.Debug("Pump will turn OFF at " + str(self.stoppump))
            else :
                self.pumpon = False # We are not yet in the period of filtration
                if Devices[3].nValue == 1:
                    Devices[3].Update(nValue=0, sValue=Devices[3].sValue)
                    DomoticzAPI("type=command&param=switchlight&idx={}&switchcmd=Off".format(self.pumpidx))
                    self.pumporderchangedtime = datetime.now()
                Domoticz.Debug("Pump is OFF - Will turn ON at " + str(self.startpump))
                Domoticz.Debug("Next Filtration calcul. dur. will be : " + str(self.PumpTemp))
            if self.pumpon :
                if self.stoppump < now : # We are in the period of filtration and we leave it, stop pump
                    self.pumpon = False
                    if Devices[3].nValue == 1:
                        Devices[3].Update(nValue=0, sValue=Devices[3].sValue)
                        DomoticzAPI("type=command&param=switchlight&idx={}&switchcmd=Off".format(self.pumpidx))
                        self.pumporderchangedtime = datetime.now()
                    Domoticz.Debug("Pump turned OFF after daily period at : " + str(self.stoppump))
                    Domoticz.Debug("Past Filtration calcul. dur. was : " + str(self.PumpTemp))
            self.PumpTempRounded = round(float(self.PumpTemp))  # pas chiffre apres la virgule
            #Devices[11].Update(nValue=0, sValue="Auto - Calcul. {}H/24".format(self.PumpTempRounded))
            #(self.startpump.hour, self.startpump.minute, self.stoppump.hour, self.stoppump.minute)
            T1 = self.startpump
            Domoticz.Debug("T1 is {}".format(T1))
            T2 = self.stoppump
            Domoticz.Debug("T2 is {}".format(T1))
            '''StartH = T1.strftime("%-H")
            StartM = T1.strftime("%M")
            StopH = T2.strftime("%-H")
            StopM = T2.strftime("%M")
            Devices[11].Update(nValue=0, sValue="Auto - Calcul. {}H - {}:{} -> {}:{}".format(self.PumpTempRounded, StartH, StartM, StopH, StopM)'''
        # be sure each 15 mins relay take the real good order and position, main for auto mode
        if not self.forced :
            if self.pumporderchangedtime + timedelta(minutes=15) < now:
                self.pumporderchangedtime = datetime.now()
                if self.pumpon :
                    DomoticzAPI("type=command&param=switchlight&idx={}&switchcmd=On".format(self.pumpidx))
                else :
                    DomoticzAPI("type=command&param=switchlight&idx={}&switchcmd=Off".format(self.pumpidx))
        else :
            if Devices[3].nValue == 0:
                Devices[3].Update(nValue=1, sValue=Devices[3].sValue)
                DomoticzAPI("type=command&param=switchlight&idx={}&switchcmd=On".format(self.pumpidx))
                self.pumponstarttime = datetime.now()

        # Temp ---------------------------------------------------
        if self.powerOn and Devices[3].nValue == 1:  # On in manual or in Auto and filtration is On
            if (Devices[2].sValue == "20"): # Heating forced
                self.Heating = True
                if Devices[6].nValue == 0:
                    Devices[6].Update(nValue=1, sValue=Devices[6].sValue)
                    Domoticz.Debug("Heating is FORCED ON")
            elif (Devices[2].sValue == "10"): # Heating Auto with 1 for hysterisis low
                if self.SPTemp < (float(Devices[5].sValue) - 1):
                    self.Heating = True
                    if Devices[6].nValue == 0:
                        Devices[6].Update(nValue=1, sValue=Devices[6].sValue)
                    Domoticz.Debug("Heating is AUTO ON - Heating requested")
                if self.SPTemp > (float(Devices[5].sValue) + 0.1):
                    self.Heating = False
                    if Devices[6].nValue == 1:
                        Devices[6].Update(nValue=0, sValue=Devices[6].sValue)
                    Domoticz.Debug("Heating is AUTO OFF - No heating requested")
            else : # Heating off
                self.Heating = False
                if Devices[6].nValue == 1:
                    Devices[6].Update(nValue=0, sValue=Devices[6].sValue)
                Domoticz.Debug("Heating is OFF")
        else :
            self.Heating = False
            if Devices[6].nValue == 1:
                Devices[6].Update(nValue=0, sValue=Devices[6].sValue)
            Domoticz.Debug("Heating is OFF Because of system OFF")

# Read Analyzer---------------------------------------------------------------------------------------------
    def readAnalyzer(self):
        Domoticz.Debug("readAnalyzer called")
        self.nextAnalyzer = datetime.now()
        noerror = True
        # PH
        jsonData1 = DomoticzAPI("type=command&param=getdevices&rid={}".format(self.PHValidx))
        if jsonData1:
            for device in jsonData1["result"]:
                if "Data" in device:
                    self.PHVal = float(device["Data"])
                    Devices[8].Update(nValue=0, sValue=str(self.PHVal))  # update the dummy device
                    Domoticz.Debug("SP PH = {}".format(self.PHVal))
                    if (self.PHVal >= 7.2) and (self.PHVal < 7.6) :
                        Devices[7].Update(nValue=1, sValue="Parfait") # update the dummy device 0-gris 1-vert 2-yellow 3-orange 4-red
                    elif (self.PHVal >= 6.9) and (self.PHVal < 7.2) :
                        Devices[7].Update(nValue=3, sValue="Legerement bas")
                    elif self.PHVal < 6.9 :
                        Devices[7].Update(nValue=4, sValue="Trop Bas")
                    elif (self.PHVal >= 7.6) and (self.PHVal < 7.8) :
                        Devices[7].Update(nValue=3, sValue="Legerement haut")
                    else :
                        Devices[7].Update(nValue=4, sValue="Trop Haut")
        # Redox
        jsonData2 = DomoticzAPI("type=command&param=getdevices&rid={}".format(self.RedoxValidx))
        if jsonData2:
            for device in jsonData2["result"]:
                if "Data" in device:
                    self.RedoxVal = float(device["Data"])
                    Devices[10].Update(nValue=0, sValue=str(self.RedoxVal))  # update the dummy device
                    Domoticz.Debug("SP Redox = {}".format(self.RedoxVal))
                    if (self.RedoxVal >= 650) and (self.RedoxVal < 751) :
                        Devices[9].Update(nValue=1, sValue="Parfait") # update the dummy device 0-gris 1-vert 2-yellow 3-orange 4-red
                    elif (self.RedoxVal >= 600) and (self.RedoxVal < 650) :
                        Devices[9].Update(nValue=3,sValue="Legerement bas")
                    elif self.RedoxVal < 600 :
                        Devices[9].Update(nValue=4, sValue="Trop bas")
                    else :
                        Devices[9].Update(nValue=4, sValue="Trop Haut")
        return noerror

# Read temp-------------------------------------------------------------------------------------------------
    def readTemps(self):
        Domoticz.Debug("readTemps called")
        self.nexttemps = datetime.now()
        # fetch all the devices from the API and scan for sensors
        noerror = True
        listintemps = []
        devicesAPI = DomoticzAPI("type=command&param=getdevices&filter=temp&used=true&order=Name")
        if devicesAPI:
            for device in devicesAPI["result"]:  # parse the devices for temperature sensors
                idx = int(device["idx"])
                if idx in self.TempSensors:
                    if "Temp" in device:
                        Domoticz.Debug("device: {}-{} = {}".format(device["idx"], device["Name"], device["Temp"]))
                        listintemps.append(device["Temp"])
                    else:
                        Domoticz.Error("device: {}-{} is not a Temperature sensor".format(device["idx"], device["Name"]))
                if self.OppSPTempSens :
                    if self.pumpon :
                        now = datetime.now()
                        if self.pumponstarttime + timedelta(minutes=60) <= now:
                            if idx in self.TempSensorsOpp:
                                if "Temp" in device:
                                    Domoticz.Debug(
                                        "device: {}-{} = {}".format(device["idx"], device["Name"], device["Temp"]))
                                    listintemps.append(device["Temp"])
                                else:
                                    Domoticz.Error(
                                        "device: {}-{} is not a Temperature sensor".format(device["idx"], device["Name"]))

        # calculate the average inside temperature
        nbtemps = len(listintemps)
        if nbtemps > 0:
            self.intemp = round(sum(listintemps) / nbtemps, 1)
            Devices[4].Update(nValue=0, sValue=str(self.intemp))  # update the dummy device
            self.SPTemp = round(float(self.intemp),1)
            self.SPTempCheck = round(float(self.intemp))
        else:
            Domoticz.Debug("No SP Temperature found... ")
            noerror = False

        Domoticz.Debug("SP Temperature = {}".format(self.SPTemp))
        return noerror

# Global  ---------------------------------------------------

global _plugin
_plugin = BasePlugin()

def onStart():
    global _plugin
    _plugin.onStart()

def onStop():
    global _plugin
    _plugin.onStop()

def onCommand(Unit, Command, Level, Hue):
    global _plugin
    _plugin.onCommand(Unit, Command, Level, Hue)

def onHeartbeat():
    global _plugin
    _plugin.onHeartbeat()

# Plugin utility functions ---------------------------------------------------

def parseCSV(strCSV):

    listvals = []
    for value in strCSV.split(","):
        try:
            val = int(value)
        except:
            pass
        else:
            listvals.append(val)
    return listvals

def DomoticzAPI(APICall):

    resultJson = None
    url = "http://127.0.0.1:8080/json.htm?{}".format(parse.quote(APICall, safe="&="))
    Domoticz.Debug("Calling domoticz API: {}".format(url))
    try:
        req = request.Request(url)
        response = request.urlopen(req)
        if response.status == 200:
            resultJson = json.loads(response.read().decode('utf-8'))
            if resultJson["status"] != "OK":
                Domoticz.Error("Domoticz API returned an error: status = {}".format(resultJson["status"]))
                resultJson = None
        else:
            Domoticz.Error("Domoticz API: http error = {}".format(response.status))
    except:
        Domoticz.Error("Error calling '{}'".format(url))
    return resultJson

def CheckParam(name, value, default):

    try:
        param = int(value)
    except ValueError:
        param = default
        Domoticz.Error("Parameter '{}' has an invalid value of '{}' ! defaut of '{}' is instead used.".format(name, value, default))
    return param

# Generic helper functions ---------------------------------------------------

def dictToQuotedString(dParams):
    result = ""
    for sKey, sValue in dParams.items():
        if result:
            result += "&"
        result += sKey + "=" + quote(str(sValue))
    return result

def DumpConfigToLog():
    for x in Parameters:
        if Parameters[x] != "":
            Domoticz.Debug("'" + x + "':'" + str(Parameters[x]) + "'")
    Domoticz.Debug("Device count: " + str(len(Devices)))
    for x in Devices:
        Domoticz.Debug("Device:           " + str(x) + " - " + str(Devices[x]))
        Domoticz.Debug("Device ID:       '" + str(Devices[x].ID) + "'")
        Domoticz.Debug("Device Name:     '" + Devices[x].Name + "'")
        Domoticz.Debug("Device nValue:    " + str(Devices[x].nValue))
        Domoticz.Debug("Device sValue:   '" + Devices[x].sValue + "'")
        Domoticz.Debug("Device LastLevel: " + str(Devices[x].LastLevel))
    return
