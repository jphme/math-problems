import PeaceableQueens.UpperBound.Generated.Even.CoreTopology
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafRange41
import PeaceableQueens.UpperBound.Generated.Even.CoreScaled40Check

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def node_box_2000 : ProfileBox := branch_box_2000
def node_box_2001 : ProfileBox := { lower := ![(0 : ℚ) / 1, (889 : ℚ) / 1280, (0 : ℚ) / 1, (247 : ℚ) / 320, (77 : ℚ) / 80, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 20, (999 : ℚ) / 1280, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2002 : ProfileBox := branch_box_2002
def node_box_2003 : ProfileBox := branch_box_2003
def node_box_2004 : ProfileBox := { lower := ![(0 : ℚ) / 1, (889 : ℚ) / 1280, (0 : ℚ) / 1, (247 : ℚ) / 320, (31 : ℚ) / 32, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 20, (999 : ℚ) / 1280, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2005 : ProfileBox := branch_box_2005
def node_box_2006 : ProfileBox := { lower := ![(0 : ℚ) / 1, (889 : ℚ) / 1280, (0 : ℚ) / 1, (247 : ℚ) / 320, (31 : ℚ) / 32, (0 : ℚ) / 1, (159 : ℚ) / 160, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 20, (999 : ℚ) / 1280, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2007 : ProfileBox := { lower := ![(0 : ℚ) / 1, (889 : ℚ) / 1280, (0 : ℚ) / 1, (247 : ℚ) / 320, (31 : ℚ) / 32, (0 : ℚ) / 1, (159 : ℚ) / 160, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (1789 : ℚ) / 2560, (1 : ℚ) / 20, (999 : ℚ) / 1280, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2008 : ProfileBox := { lower := ![(0 : ℚ) / 1, (1789 : ℚ) / 2560, (0 : ℚ) / 1, (247 : ℚ) / 320, (31 : ℚ) / 32, (0 : ℚ) / 1, (159 : ℚ) / 160, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 20, (999 : ℚ) / 1280, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2009 : ProfileBox := { lower := ![(0 : ℚ) / 1, (1789 : ℚ) / 2560, (0 : ℚ) / 1, (247 : ℚ) / 320, (31 : ℚ) / 32, (0 : ℚ) / 1, (159 : ℚ) / 160, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 20, (1987 : ℚ) / 2560, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2010 : ProfileBox := branch_box_2010
def node_box_2011 : ProfileBox := branch_box_2011
def node_box_2012 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2013 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2014 : ProfileBox := { lower := ![(0 : ℚ) / 1, (439 : ℚ) / 640, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2015 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2016 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2017 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2018 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2019 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2020 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2021 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2022 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2023 : ProfileBox := branch_box_2023
def node_box_2024 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (157 : ℚ) / 160, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2025 : ProfileBox := branch_box_2025
def node_box_2026 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (157 : ℚ) / 160, (0 : ℚ) / 1, (157 : ℚ) / 160, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2027 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 80] }
def node_box_2028 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (1 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2029 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (79 : ℚ) / 80, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 80] }
def node_box_2030 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (79 : ℚ) / 80, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 80] }
def node_box_2031 : ProfileBox := branch_box_2031
def node_box_2032 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (39 : ℚ) / 40, (1 : ℚ) / 80, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (79 : ℚ) / 80, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 80] }
def node_box_2033 : ProfileBox := branch_box_2033
def node_box_2034 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (79 : ℚ) / 80, (1 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2035 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (247 : ℚ) / 320, (79 : ℚ) / 80, (1 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 80], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (101 : ℚ) / 128, (1 : ℚ) / 1, (3 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2036 : ProfileBox := branch_box_2036
def node_box_2037 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2038 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (1 : ℚ) / 80, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2039 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2040 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2041 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2042 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (79 : ℚ) / 80, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_2043 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (867 : ℚ) / 1280, (1 : ℚ) / 20, (129 : ℚ) / 160, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2044 : ProfileBox := { lower := ![(0 : ℚ) / 1, (867 : ℚ) / 1280, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (439 : ℚ) / 640, (1 : ℚ) / 20, (129 : ℚ) / 160, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2045 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (867 : ℚ) / 1280, (1 : ℚ) / 20, (1021 : ℚ) / 1280, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2046 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (1021 : ℚ) / 1280, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (867 : ℚ) / 1280, (1 : ℚ) / 20, (129 : ℚ) / 160, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2047 : ProfileBox := branch_box_2047
def node_box_2048 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (101 : ℚ) / 128, (157 : ℚ) / 160, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (867 : ℚ) / 1280, (1 : ℚ) / 20, (1021 : ℚ) / 1280, (79 : ℚ) / 80, (1 : ℚ) / 80, (79 : ℚ) / 80, (1 : ℚ) / 40] }
def node_box_2049 : ProfileBox := branch_box_2049

def split_2001_accepted : Bool := splitNodeOK node_box_2001 node_box_2003 node_box_2004 ⟨4, by omega⟩ ((31 : ℚ) / 32)
def split_2004_accepted : Bool := splitNodeOK node_box_2004 node_box_2005 node_box_2006 ⟨6, by omega⟩ ((159 : ℚ) / 160)
def split_2006_accepted : Bool := splitNodeOK node_box_2006 node_box_2007 node_box_2008 ⟨1, by omega⟩ ((1789 : ℚ) / 2560)
def split_2008_accepted : Bool := splitNodeOK node_box_2008 node_box_2009 node_box_2010 ⟨3, by omega⟩ ((1987 : ℚ) / 2560)
def split_2012_accepted : Bool := splitNodeOK node_box_2012 node_box_2013 node_box_2014 ⟨1, by omega⟩ ((439 : ℚ) / 640)
def split_2013_accepted : Bool := splitNodeOK node_box_2013 node_box_2015 node_box_2016 ⟨3, by omega⟩ ((101 : ℚ) / 128)
def split_2014_accepted : Bool := splitNodeOK node_box_2014 node_box_2123 node_box_2124 ⟨3, by omega⟩ ((101 : ℚ) / 128)
def split_2015_accepted : Bool := splitNodeOK node_box_2015 node_box_2017 node_box_2018 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_2016_accepted : Bool := splitNodeOK node_box_2016 node_box_2037 node_box_2038 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_2017_accepted : Bool := splitNodeOK node_box_2017 node_box_2019 node_box_2020 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_2018_accepted : Bool := splitNodeOK node_box_2018 node_box_2027 node_box_2028 ⟨7, by omega⟩ ((1 : ℚ) / 80)
def split_2019_accepted : Bool := splitNodeOK node_box_2019 node_box_2021 node_box_2022 ⟨6, by omega⟩ ((79 : ℚ) / 80)
def split_2021_accepted : Bool := splitNodeOK node_box_2021 node_box_2023 node_box_2024 ⟨4, by omega⟩ ((157 : ℚ) / 160)
def split_2024_accepted : Bool := splitNodeOK node_box_2024 node_box_2025 node_box_2026 ⟨6, by omega⟩ ((157 : ℚ) / 160)
def split_2027_accepted : Bool := splitNodeOK node_box_2027 node_box_2029 node_box_2030 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_2028_accepted : Bool := splitNodeOK node_box_2028 node_box_2033 node_box_2034 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_2029_accepted : Bool := splitNodeOK node_box_2029 node_box_2031 node_box_2032 ⟨6, by omega⟩ ((79 : ℚ) / 80)
def split_2034_accepted : Bool := splitNodeOK node_box_2034 node_box_2035 node_box_2036 ⟨5, by omega⟩ ((3 : ℚ) / 160)
def split_2037_accepted : Bool := splitNodeOK node_box_2037 node_box_2039 node_box_2040 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_2038_accepted : Bool := splitNodeOK node_box_2038 node_box_2097 node_box_2098 ⟨7, by omega⟩ ((1 : ℚ) / 80)
def split_2039_accepted : Bool := splitNodeOK node_box_2039 node_box_2041 node_box_2042 ⟨6, by omega⟩ ((79 : ℚ) / 80)
def split_2040_accepted : Bool := splitNodeOK node_box_2040 node_box_2083 node_box_2084 ⟨1, by omega⟩ ((867 : ℚ) / 1280)
def split_2041_accepted : Bool := splitNodeOK node_box_2041 node_box_2043 node_box_2044 ⟨1, by omega⟩ ((867 : ℚ) / 1280)
def split_2042_accepted : Bool := splitNodeOK node_box_2042 node_box_2069 node_box_2070 ⟨1, by omega⟩ ((867 : ℚ) / 1280)
def split_2043_accepted : Bool := splitNodeOK node_box_2043 node_box_2045 node_box_2046 ⟨3, by omega⟩ ((1021 : ℚ) / 1280)
def split_2044_accepted : Bool := splitNodeOK node_box_2044 node_box_2059 node_box_2060 ⟨3, by omega⟩ ((1021 : ℚ) / 1280)
def split_2045_accepted : Bool := splitNodeOK node_box_2045 node_box_2047 node_box_2048 ⟨4, by omega⟩ ((157 : ℚ) / 160)
def split_2046_accepted : Bool := splitNodeOK node_box_2046 node_box_2051 node_box_2052 ⟨4, by omega⟩ ((157 : ℚ) / 160)
def split_2048_accepted : Bool := splitNodeOK node_box_2048 node_box_2049 node_box_2050 ⟨6, by omega⟩ ((157 : ℚ) / 160)
def split_batch_40_values : List Bool := [split_2001_accepted, split_2004_accepted, split_2006_accepted, split_2008_accepted, split_2012_accepted, split_2013_accepted, split_2014_accepted, split_2015_accepted, split_2016_accepted, split_2017_accepted, split_2018_accepted, split_2019_accepted, split_2021_accepted, split_2024_accepted, split_2027_accepted, split_2028_accepted, split_2029_accepted, split_2034_accepted, split_2037_accepted, split_2038_accepted, split_2039_accepted, split_2040_accepted, split_2041_accepted, split_2042_accepted, split_2043_accepted, split_2044_accepted, split_2045_accepted, split_2046_accepted, split_2048_accepted]
theorem split_batch_40_ok : split_batch_40_values.all id = true := by
  native_decide

def terminal_2007_accepted : Bool := LeafChecks.checkCore node_box_2007
def terminal_2009_accepted : Bool := LeafChecks.checkCore node_box_2009
def terminal_2020_accepted : Bool := LeafChecks.checkCore node_box_2020
def terminal_2022_accepted : Bool := LeafChecks.checkCore node_box_2022
def terminal_2026_accepted : Bool := LeafChecks.checkCore node_box_2026
def terminal_2030_accepted : Bool := LeafChecks.checkCore node_box_2030
def terminal_2032_accepted : Bool := LeafChecks.checkCore node_box_2032
def terminal_2035_accepted : Bool := LeafChecks.checkCore node_box_2035
def terminal_batch_40_values : List Bool := [terminal_2007_accepted, terminal_2009_accepted, terminal_2020_accepted, terminal_2022_accepted, terminal_2026_accepted, terminal_2030_accepted, terminal_2032_accepted, terminal_2035_accepted]
theorem terminal_batch_40_ok : terminal_batch_40_values.all id = true := by
  native_decide

theorem tree_2049 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2049) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2049] using leaf_2049_BranchSafe))⟩

theorem split_2048_ok : split_2048_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2048_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2048 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2048) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2048 node_box_2049 node_box_2050 ⟨6, by omega⟩ ((157 : ℚ) / 160)
    (by simpa [split_2048_accepted] using split_2048_ok) tree_2049 tree_2050

theorem tree_2047 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2047) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2047] using leaf_2047_BranchSafe))⟩

theorem split_2046_ok : split_2046_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2046_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2046 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2046) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2046 node_box_2051 node_box_2052 ⟨4, by omega⟩ ((157 : ℚ) / 160)
    (by simpa [split_2046_accepted] using split_2046_ok) tree_2051 tree_2052

theorem split_2045_ok : split_2045_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2045_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2045 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2045) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2045 node_box_2047 node_box_2048 ⟨4, by omega⟩ ((157 : ℚ) / 160)
    (by simpa [split_2045_accepted] using split_2045_ok) tree_2047 tree_2048

theorem split_2044_ok : split_2044_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2044_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2044 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2044) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2044 node_box_2059 node_box_2060 ⟨3, by omega⟩ ((1021 : ℚ) / 1280)
    (by simpa [split_2044_accepted] using split_2044_ok) tree_2059 tree_2060

theorem split_2043_ok : split_2043_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2043_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2043 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2043) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2043 node_box_2045 node_box_2046 ⟨3, by omega⟩ ((1021 : ℚ) / 1280)
    (by simpa [split_2043_accepted] using split_2043_ok) tree_2045 tree_2046

theorem split_2042_ok : split_2042_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2042_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2042 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2042) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2042 node_box_2069 node_box_2070 ⟨1, by omega⟩ ((867 : ℚ) / 1280)
    (by simpa [split_2042_accepted] using split_2042_ok) tree_2069 tree_2070

theorem split_2041_ok : split_2041_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2041_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2041 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2041) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2041 node_box_2043 node_box_2044 ⟨1, by omega⟩ ((867 : ℚ) / 1280)
    (by simpa [split_2041_accepted] using split_2041_ok) tree_2043 tree_2044

theorem split_2040_ok : split_2040_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2040_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2040 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2040) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2040 node_box_2083 node_box_2084 ⟨1, by omega⟩ ((867 : ℚ) / 1280)
    (by simpa [split_2040_accepted] using split_2040_ok) tree_2083 tree_2084

theorem split_2039_ok : split_2039_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2039_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2039 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2039) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2039 node_box_2041 node_box_2042 ⟨6, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_2039_accepted] using split_2039_ok) tree_2041 tree_2042

theorem split_2038_ok : split_2038_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2038_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2038 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2038) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2038 node_box_2097 node_box_2098 ⟨7, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_2038_accepted] using split_2038_ok) tree_2097 tree_2098

theorem split_2037_ok : split_2037_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2037_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2037 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2037) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2037 node_box_2039 node_box_2040 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_2037_accepted] using split_2037_ok) tree_2039 tree_2040

theorem tree_2036 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2036) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2036] using leaf_2036_BranchSafe))⟩

theorem terminal_2035_ok : terminal_2035_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_40_ok terminal_2035_accepted
    (by simp [terminal_batch_40_values])
  exact h
theorem tree_2035 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2035) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_2035
  simpa [terminal_2035_accepted] using terminal_2035_ok

theorem split_2034_ok : split_2034_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2034_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2034 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2034) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2034 node_box_2035 node_box_2036 ⟨5, by omega⟩ ((3 : ℚ) / 160)
    (by simpa [split_2034_accepted] using split_2034_ok) tree_2035 tree_2036

theorem tree_2033 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2033) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2033] using leaf_2033_BranchSafe))⟩

theorem terminal_2032_ok : terminal_2032_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_40_ok terminal_2032_accepted
    (by simp [terminal_batch_40_values])
  exact h
theorem tree_2032 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2032) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_2032
  simpa [terminal_2032_accepted] using terminal_2032_ok

theorem tree_2031 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2031) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2031] using leaf_2031_BranchSafe))⟩

theorem terminal_2030_ok : terminal_2030_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_40_ok terminal_2030_accepted
    (by simp [terminal_batch_40_values])
  exact h
theorem tree_2030 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2030) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_2030
  simpa [terminal_2030_accepted] using terminal_2030_ok

theorem split_2029_ok : split_2029_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2029_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2029 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2029) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2029 node_box_2031 node_box_2032 ⟨6, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_2029_accepted] using split_2029_ok) tree_2031 tree_2032

theorem split_2028_ok : split_2028_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2028_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2028 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2028) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2028 node_box_2033 node_box_2034 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_2028_accepted] using split_2028_ok) tree_2033 tree_2034

theorem split_2027_ok : split_2027_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2027_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2027 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2027) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2027 node_box_2029 node_box_2030 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_2027_accepted] using split_2027_ok) tree_2029 tree_2030

theorem terminal_2026_ok : terminal_2026_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_40_ok terminal_2026_accepted
    (by simp [terminal_batch_40_values])
  exact h
theorem tree_2026 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2026) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_2026
  simpa [terminal_2026_accepted] using terminal_2026_ok

theorem tree_2025 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2025) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2025] using leaf_2025_BranchSafe))⟩

theorem split_2024_ok : split_2024_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2024_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2024 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2024) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2024 node_box_2025 node_box_2026 ⟨6, by omega⟩ ((157 : ℚ) / 160)
    (by simpa [split_2024_accepted] using split_2024_ok) tree_2025 tree_2026

theorem tree_2023 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2023) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2023] using leaf_2023_BranchSafe))⟩

theorem terminal_2022_ok : terminal_2022_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_40_ok terminal_2022_accepted
    (by simp [terminal_batch_40_values])
  exact h
theorem tree_2022 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2022) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_2022
  simpa [terminal_2022_accepted] using terminal_2022_ok

theorem split_2021_ok : split_2021_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2021_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2021 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2021) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2021 node_box_2023 node_box_2024 ⟨4, by omega⟩ ((157 : ℚ) / 160)
    (by simpa [split_2021_accepted] using split_2021_ok) tree_2023 tree_2024

theorem terminal_2020_ok : terminal_2020_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_40_ok terminal_2020_accepted
    (by simp [terminal_batch_40_values])
  exact h
theorem tree_2020 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2020) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_2020
  simpa [terminal_2020_accepted] using terminal_2020_ok

theorem split_2019_ok : split_2019_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2019_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2019 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2019) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2019 node_box_2021 node_box_2022 ⟨6, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_2019_accepted] using split_2019_ok) tree_2021 tree_2022

theorem split_2018_ok : split_2018_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2018_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2018 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2018) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2018 node_box_2027 node_box_2028 ⟨7, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_2018_accepted] using split_2018_ok) tree_2027 tree_2028

theorem split_2017_ok : split_2017_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2017_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2017 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2017) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2017 node_box_2019 node_box_2020 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_2017_accepted] using split_2017_ok) tree_2019 tree_2020

theorem split_2016_ok : split_2016_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2016_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2016 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2016) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2016 node_box_2037 node_box_2038 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_2016_accepted] using split_2016_ok) tree_2037 tree_2038

theorem split_2015_ok : split_2015_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2015_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2015 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2015) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2015 node_box_2017 node_box_2018 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_2015_accepted] using split_2015_ok) tree_2017 tree_2018

theorem split_2014_ok : split_2014_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2014_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2014 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2014) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2014 node_box_2123 node_box_2124 ⟨3, by omega⟩ ((101 : ℚ) / 128)
    (by simpa [split_2014_accepted] using split_2014_ok) tree_2123 tree_2124

theorem split_2013_ok : split_2013_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2013_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2013 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2013) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2013 node_box_2015 node_box_2016 ⟨3, by omega⟩ ((101 : ℚ) / 128)
    (by simpa [split_2013_accepted] using split_2013_ok) tree_2015 tree_2016

theorem split_2012_ok : split_2012_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2012_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2012 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2012) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2012 node_box_2013 node_box_2014 ⟨1, by omega⟩ ((439 : ℚ) / 640)
    (by simpa [split_2012_accepted] using split_2012_ok) tree_2013 tree_2014

theorem tree_2011 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2011) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2011] using leaf_2011_BranchSafe))⟩

theorem tree_2010 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2010) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2010] using leaf_2010_BranchSafe))⟩

theorem terminal_2009_ok : terminal_2009_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_40_ok terminal_2009_accepted
    (by simp [terminal_batch_40_values])
  exact h
theorem tree_2009 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2009) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_2009
  simpa [terminal_2009_accepted] using terminal_2009_ok

theorem split_2008_ok : split_2008_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2008_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2008 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2008) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2008 node_box_2009 node_box_2010 ⟨3, by omega⟩ ((1987 : ℚ) / 2560)
    (by simpa [split_2008_accepted] using split_2008_ok) tree_2009 tree_2010

theorem terminal_2007_ok : terminal_2007_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_40_ok terminal_2007_accepted
    (by simp [terminal_batch_40_values])
  exact h
theorem tree_2007 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2007) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_2007
  simpa [terminal_2007_accepted] using terminal_2007_ok

theorem split_2006_ok : split_2006_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2006_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2006 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2006) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2006 node_box_2007 node_box_2008 ⟨1, by omega⟩ ((1789 : ℚ) / 2560)
    (by simpa [split_2006_accepted] using split_2006_ok) tree_2007 tree_2008

theorem tree_2005 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2005) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2005] using leaf_2005_BranchSafe))⟩

theorem split_2004_ok : split_2004_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2004_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2004 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2004) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2004 node_box_2005 node_box_2006 ⟨6, by omega⟩ ((159 : ℚ) / 160)
    (by simpa [split_2004_accepted] using split_2004_ok) tree_2005 tree_2006

theorem tree_2003 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2003) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2003] using leaf_2003_BranchSafe))⟩

theorem tree_2002 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2002) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2002] using leaf_2002_BranchSafe))⟩

theorem split_2001_ok : split_2001_accepted = true := by
  have h := List.all_eq_true.mp split_batch_40_ok split_2001_accepted
    (by simp [split_batch_40_values])
  exact h
theorem tree_2001 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2001) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2001 node_box_2003 node_box_2004 ⟨4, by omega⟩ ((31 : ℚ) / 32)
    (by simpa [split_2001_accepted] using split_2001_ok) tree_2003 tree_2004

theorem tree_2000 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2000) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_2000] using leaf_2000_BranchSafe))⟩

#print axioms tree_2000
end PeaceableQueens.UpperBound.Generated.Even.Core
