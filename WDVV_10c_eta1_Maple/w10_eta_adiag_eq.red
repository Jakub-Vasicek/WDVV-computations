% 2021-04-19, JV
% some adjustments in notation for Maple were made
% WDVV equations for eta2


The_WDVV_system:=[2*f_2zw*f_xzw - f_3z*f_x2w - f_x2z*f_z2w - f_y2w*f_y2z + f_yzw
**2,
f_2yw*f_yzw - f_2yz*f_y2w + f_2zw*f_xyw - f_x2w*f_y2z - f_xyz*f_z2w + f_xzw*
f_yzw,
f_2yw*f_y2z - f_2yz*f_yzw - f_2zw*f_xyz + f_3z*f_xyw + f_x2z*f_yzw - f_xzw*f_y2z
,
f_2yw**2 - f_2yz*f_x2w - f_3w - f_3y*f_y2w - f_x2y*f_z2w + 2*f_xyw*f_yzw,
f_2yw*f_2yz - f_2yz*f_xzw - f_2zw*f_x2y - f_3y*f_yzw + f_xyw*f_y2z + f_xyz*f_yzw
 - f_z2w,
f_2yz**2 - f_2yz*f_x2z - f_2zw - f_3y*f_y2z - f_3z*f_x2y + 2*f_xyz*f_y2z,
f_2xw*f_2zw - f_2xz*f_z2w - f_3w - f_x2w*f_x2z + f_xyw*f_yzw - f_xyz*f_y2w + 
f_xzw**2,
f_2xw*f_3z - f_2xz*f_2zw + f_xyw*f_y2z - f_xyz*f_yzw - f_z2w,
f_2xw*f_y2z - f_2xz*f_yzw - f_2yw*f_xyz + f_2yz*f_xyw - f_x2z*f_xyw + f_xyz*
f_xzw - f_y2w,
f_2xw*f_yzw - f_2xy*f_z2w + f_2yw*f_xyw - f_x2w*f_xyz - f_x2y*f_y2w + f_xyw*
f_xzw,
f_2xw*f_y2z - f_2xy*f_2zw + f_2yz*f_xyw - f_x2y*f_yzw,
f_2xw*f_2yz - f_2xy*f_yzw - f_2yw*f_x2y + f_3y*f_xyw + f_x2w + f_x2y*f_xzw - 
f_xyw*f_xyz,
 - f_2xy*f_2zw + f_2xz*f_yzw + f_2yw*f_xyz - f_x2y*f_yzw + f_x2z*f_xyw - f_xyz*
f_xzw + f_y2w,
 - f_2xy*f_3z + f_2xz*f_y2z + f_2yz*f_xyz - f_x2y*f_y2z + f_yzw,
 - f_2xy*f_y2z + f_2xz*f_2yz + f_2yw - f_2yz*f_x2y + f_3y*f_xyz + f_x2y*f_x2z - 
f_xyz**2 + f_xzw,
2*f_2xw*f_xzw - f_2xy*f_y2w - f_2xz*f_x2w - f_3x*f_z2w + f_xyw**2,
f_2xw*f_x2z - f_2xy*f_yzw - f_2zw*f_3x + f_x2w + f_xyw*f_xyz,
 - f_2xy*f_y2z + f_2xz*f_x2z - f_3x*f_3z + f_xyz**2 + 2*f_xzw,
f_2xw*f_xyz - f_2xy*f_2yw + f_2xy*f_xzw - f_2xz*f_xyw - f_3x*f_yzw + f_x2y*f_xyw
,
 - f_2xy*f_2yz + f_2xy*f_x2z - f_3x*f_y2z + f_x2y*f_xyz + f_xyw,
 - f_2xw - f_2xy*f_3y + 2*f_2xy*f_xyz - f_2xz*f_x2y - f_2yz*f_3x + f_x2y**2]:


cons_laws_system:=[[f_3x,f_2xy],
[f_2xy,f_x2y],
[f_2xz,f_xyz],
[f_2xw,f_xyw],
[f_x2y,
( - f_2xw**2*f_3x**2 + f_2xw*f_2xy**4 + f_2xw*f_2xy**2*f_2xz*f_3x - 2*f_2xw*
f_2xy**2*f_3x*f_x2y + f_2xw*f_2xy*f_3x**2*f_xyz - 2*f_2xw*f_2xz*f_3x**2*f_x2y + 
2*f_2xw*f_3x**2*f_x2y**2 - 2*f_2xy**5*f_xyz + f_2xy**4*f_2xz*f_x2y + f_2xy**4*
f_3x*f_x2z - f_2xy**4*f_x2y**2 - 2*f_2xy**3*f_2xz*f_3x*f_xyz + 5*f_2xy**3*f_3x*
f_x2y*f_xyz + f_2xy**3*f_3x*f_xyw + f_2xy**2*f_2xz**2*f_3x*f_x2y - 3*f_2xy**2*
f_2xz*f_3x*f_x2y**2 - 2*f_2xy**2*f_3x**2*f_x2y*f_x2z + f_2xy**2*f_3x**2*f_xyz**2
 - 2*f_2xy**2*f_3x**2*f_xzw + 2*f_2xy**2*f_3x*f_x2y**3 + 2*f_2xy*f_2xz*f_3x**2*
f_x2y*f_xyz + f_2xy*f_2xz*f_3x**2*f_xyw - 3*f_2xy*f_3x**2*f_x2y**2*f_xyz - 2*
f_2xy*f_3x**2*f_x2y*f_xyw - f_2xz**2*f_3x**2*f_x2y**2 + 2*f_2xz*f_3x**2*f_x2y**3
 + f_3x**3*f_x2w + f_3x**3*f_x2y**2*f_x2z - f_3x**3*f_x2y*f_xyz**2 + 2*f_3x**3*
f_x2y*f_xzw - f_3x**3*f_xyw*f_xyz - f_3x**2*f_x2y**4)/(f_2xw*f_2xy*f_3x**2 - 
f_2xy**5 - f_2xy**3*f_2xz*f_3x + 2*f_2xy**3*f_3x*f_x2y + f_2xy**2*f_3x**2*f_xyz 
+ f_2xy*f_2xz*f_3x**2*f_x2y - f_2xy*f_3x**2*f_x2y**2 - f_3x**3*f_x2y*f_xyz - 
f_3x**3*f_xyw)],
[f_xyz,
(f_2xw*f_3x**2*f_x2y*f_xyz + f_2xw*f_3x**2*f_xyw - f_2xy**5*f_x2z - f_2xy**4*
f_x2y*f_xyz - f_2xy**4*f_xyw + 2*f_2xy**3*f_3x*f_x2y*f_x2z + f_2xy**3*f_3x*f_xyz
**2 + 2*f_2xy**3*f_3x*f_xzw - f_2xy**2*f_2xz*f_3x*f_x2y*f_xyz - f_2xy**2*f_2xz*
f_3x*f_xyw + 2*f_2xy**2*f_3x*f_x2y**2*f_xyz + 2*f_2xy**2*f_3x*f_x2y*f_xyw - 
f_2xy*f_3x**2*f_x2w - f_2xy*f_3x**2*f_x2y**2*f_x2z - f_2xy*f_3x**2*f_x2y*f_xyz**
2 - 2*f_2xy*f_3x**2*f_x2y*f_xzw - f_2xy*f_3x**2*f_xyw*f_xyz + f_2xz*f_3x**2*
f_x2y**2*f_xyz + f_2xz*f_3x**2*f_x2y*f_xyw - f_3x**2*f_x2y**3*f_xyz - f_3x**2*
f_x2y**2*f_xyw)/(f_2xw*f_2xy*f_3x**2 - f_2xy**5 - f_2xy**3*f_2xz*f_3x + 2*f_2xy
**3*f_3x*f_x2y + f_2xy**2*f_3x**2*f_xyz + f_2xy*f_2xz*f_3x**2*f_x2y - f_2xy*f_3x
**2*f_x2y**2 - f_3x**3*f_x2y*f_xyz - f_3x**3*f_xyw)],
[f_x2z,
(f_2xw*f_2xy**2*f_3x*f_x2z - f_2xy**4*f_2xz*f_x2z - f_2xy**4*f_xyz**2 - 2*f_2xy
**4*f_xzw + f_2xy**3*f_3x*f_x2z*f_xyz + f_2xy**2*f_2xz*f_3x*f_x2y*f_x2z + f_2xy
**2*f_3x*f_x2w + 2*f_2xy**2*f_3x*f_x2y*f_xyz**2 + 2*f_2xy**2*f_3x*f_x2y*f_xzw + 
2*f_2xy**2*f_3x*f_xyw*f_xyz - f_2xy*f_3x**2*f_x2y*f_x2z*f_xyz - f_2xy*f_3x**2*
f_x2z*f_xyw - f_3x**2*f_x2y**2*f_xyz**2 - 2*f_3x**2*f_x2y*f_xyw*f_xyz - f_3x**2*
f_xyw**2)/(f_2xw*f_2xy*f_3x**2 - f_2xy**5 - f_2xy**3*f_2xz*f_3x + 2*f_2xy**3*
f_3x*f_x2y + f_2xy**2*f_3x**2*f_xyz + f_2xy*f_2xz*f_3x**2*f_x2y - f_2xy*f_3x**2*
f_x2y**2 - f_3x**3*f_x2y*f_xyz - f_3x**3*f_xyw)],
[f_xyw,
(f_2xw**2*f_3x**2*f_xyz - f_2xw*f_2xy**4*f_xyz + f_2xw*f_2xy**3*f_3x*f_x2z - 
f_2xw*f_2xy**2*f_2xz*f_3x*f_xyz + 2*f_2xw*f_2xy**2*f_3x*f_x2y*f_xyz - f_2xw*
f_2xy*f_3x**2*f_x2y*f_x2z - f_2xw*f_2xy*f_3x**2*f_xzw + f_2xw*f_2xz*f_3x**2*
f_x2y*f_xyz - f_2xw*f_2xz*f_3x**2*f_xyw - f_2xw*f_3x**2*f_x2y**2*f_xyz + f_2xw*
f_3x**2*f_x2y*f_xyw - f_2xy**5*f_xzw + f_2xy**4*f_2xz*f_xyw - f_2xy**4*f_x2y*
f_xyw - f_2xy**3*f_2xz*f_3x*f_xzw + f_2xy**3*f_3x*f_x2w + 2*f_2xy**3*f_3x*f_x2y*
f_xzw + f_2xy**3*f_3x*f_xyw*f_xyz + f_2xy**2*f_2xz**2*f_3x*f_xyw - 3*f_2xy**2*
f_2xz*f_3x*f_x2y*f_xyw - f_2xy**2*f_3x**2*f_x2z*f_xyw + f_2xy**2*f_3x**2*f_xyz*
f_xzw + 2*f_2xy**2*f_3x*f_x2y**2*f_xyw + f_2xy*f_2xz*f_3x**2*f_x2w + f_2xy*f_2xz
*f_3x**2*f_x2y*f_xzw - f_2xy*f_3x**2*f_x2w*f_x2y - f_2xy*f_3x**2*f_x2y**2*f_xzw 
- f_2xy*f_3x**2*f_x2y*f_xyw*f_xyz - f_2xy*f_3x**2*f_xyw**2 - f_2xz**2*f_3x**2*
f_x2y*f_xyw + 2*f_2xz*f_3x**2*f_x2y**2*f_xyw - f_3x**3*f_x2w*f_xyz + f_3x**3*
f_x2y*f_x2z*f_xyw - f_3x**3*f_x2y*f_xyz*f_xzw + f_3x**3*f_xyw*f_xzw - f_3x**2*
f_x2y**3*f_xyw)/(f_2xw*f_2xy*f_3x**2 - f_2xy**5 - f_2xy**3*f_2xz*f_3x + 2*f_2xy
**3*f_3x*f_x2y + f_2xy**2*f_3x**2*f_xyz + f_2xy*f_2xz*f_3x**2*f_x2y - f_2xy*f_3x
**2*f_x2y**2 - f_3x**3*f_x2y*f_xyz - f_3x**3*f_xyw)],
[f_xzw,
( - f_2xw*f_2xy**4*f_x2z + f_2xw*f_2xy**2*f_3x*f_x2y*f_x2z + f_2xw*f_2xy**2*f_3x
*f_xyz**2 + 2*f_2xw*f_2xy**2*f_3x*f_xzw - f_2xw*f_3x**2*f_x2y*f_xyz**2 - f_2xw*
f_3x**2*f_xyw*f_xyz - f_2xy**4*f_x2w - f_2xy**4*f_xyw*f_xyz + f_2xy**3*f_3x*
f_x2z*f_xyw - f_2xy**2*f_2xz*f_3x*f_x2w - f_2xy**2*f_2xz*f_3x*f_xyw*f_xyz + 
f_2xy**2*f_3x*f_x2w*f_x2y + 2*f_2xy**2*f_3x*f_x2y*f_xyw*f_xyz + f_2xy**2*f_3x*
f_xyw**2 + f_2xy*f_3x**2*f_x2w*f_xyz - f_2xy*f_3x**2*f_x2y*f_x2z*f_xyw - 2*f_2xy
*f_3x**2*f_xyw*f_xzw + f_2xz*f_3x**2*f_x2y*f_xyw*f_xyz + f_2xz*f_3x**2*f_xyw**2 
- f_3x**2*f_x2y**2*f_xyw*f_xyz - f_3x**2*f_x2y*f_xyw**2)/(f_2xw*f_2xy*f_3x**2 - 
f_2xy**5 - f_2xy**3*f_2xz*f_3x + 2*f_2xy**3*f_3x*f_x2y + f_2xy**2*f_3x**2*f_xyz 
+ f_2xy*f_2xz*f_3x**2*f_x2y - f_2xy*f_3x**2*f_x2y**2 - f_3x**3*f_x2y*f_xyz - 
f_3x**3*f_xyw)],
[f_x2w,
(f_2xw**2*f_2xy**2*f_3x*f_x2z - f_2xw**2*f_3x**2*f_xyz**2 - 2*f_2xw*f_2xy**4*
f_xzw - 2*f_2xw*f_2xy**2*f_2xz*f_3x*f_xzw + f_2xw*f_2xy**2*f_3x*f_x2w + 2*f_2xw*
f_2xy**2*f_3x*f_x2y*f_xzw + 2*f_2xw*f_2xy**2*f_3x*f_xyw*f_xyz - 2*f_2xw*f_2xy*
f_3x**2*f_x2z*f_xyw + 2*f_2xw*f_2xy*f_3x**2*f_xyz*f_xzw + 2*f_2xw*f_2xz*f_3x**2*
f_xyw*f_xyz - 2*f_2xw*f_3x**2*f_x2y*f_xyw*f_xyz + f_2xy**4*f_2xz*f_x2w - f_2xy**
4*f_xyw**2 - f_2xy**3*f_3x*f_x2w*f_xyz + 2*f_2xy**3*f_3x*f_xyw*f_xzw + f_2xy**2*
f_2xz**2*f_3x*f_x2w - f_2xy**2*f_2xz*f_3x*f_x2w*f_x2y - 2*f_2xy**2*f_2xz*f_3x*
f_xyw**2 + 2*f_2xy**2*f_3x*f_x2y*f_xyw**2 - 2*f_2xy*f_2xz*f_3x**2*f_x2w*f_xyz + 
2*f_2xy*f_2xz*f_3x**2*f_xyw*f_xzw + f_2xy*f_3x**2*f_x2w*f_x2y*f_xyz - f_2xy*f_3x
**2*f_x2w*f_xyw - 2*f_2xy*f_3x**2*f_x2y*f_xyw*f_xzw - f_2xz**2*f_3x**2*f_xyw**2 
+ 2*f_2xz*f_3x**2*f_x2y*f_xyw**2 + f_3x**3*f_x2w*f_xyz**2 + f_3x**3*f_x2z*f_xyw
**2 - 2*f_3x**3*f_xyw*f_xyz*f_xzw - f_3x**2*f_x2y**2*f_xyw**2)/(f_2xw*f_2xy*f_3x
**2 - f_2xy**5 - f_2xy**3*f_2xz*f_3x + 2*f_2xy**3*f_3x*f_x2y + f_2xy**2*f_3x**2*
f_xyz + f_2xy*f_2xz*f_3x**2*f_x2y - f_2xy*f_3x**2*f_x2y**2 - f_3x**3*f_x2y*f_xyz
 - f_3x**3*f_xyw)]]:


;end;

