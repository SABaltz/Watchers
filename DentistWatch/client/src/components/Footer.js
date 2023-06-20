import React from "react";
import AppBar from "@mui/material/AppBar";
import Box from "@mui/material/Box";
import Toolbar from "@mui/material/Toolbar";
import Typography from "@mui/material/Typography";
import {Grid} from "@mui/material";

export default function Footer() {
    return (
        <Box sx={{flexGrow: 1}}>
            <AppBar osition="fixed" color="primary" sx={{top: 'auto', bottom: 0}}>
                <Toolbar>
                    <Grid container>
                        <Grid item xs={2}>
                            <Typography variant="h6" component="div" sx={{flexGrow: 1}}>
                                Home
                            </Typography>
                        </Grid>
                        <Grid item xs={2}>
                            <Typography variant="h6" component="div" sx={{flexGrow: 1}}>
                                About
                            </Typography>
                        </Grid>
                        <Grid item xs={2}>
                            <Typography variant="h6" component="div" sx={{flexGrow: 1}}>
                                Contact
                            </Typography>
                        </Grid>
                        <Grid itexs={2}>
                            <Typography variant="h6" component="div" sx={{flexGrow: 1}}>
                                @Dentist Watch | All Rights Reserved
                            </Typography>
                        </Grid>
                    </Grid>
                </Toolbar>
            </AppBar>
        </Box>
    )
}
