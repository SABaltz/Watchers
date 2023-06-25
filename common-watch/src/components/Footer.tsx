import React from "react";
import AppBar from "@mui/material/AppBar";
import Box from "@mui/material/Box";
import Toolbar from "@mui/material/Toolbar";
import Typography from "@mui/material/Typography";
import {Grid} from "@mui/material";

export default function Footer() {
    return (
        <Box>
            <AppBar position="static" color="primary">
                <Toolbar>
                    <Grid container>
                        <Grid item xs={9}>
                            <Grid container>
                                <Grid item xs={2}>
                                    <Typography variant="subtitle1" component="div">
                                        Home
                                    </Typography>
                                </Grid>
                                <Grid item xs={2}>
                                    <Typography variant="subtitle1" component="div">
                                        About
                                    </Typography>
                                </Grid>
                                <Grid item xs={2}>
                                    <Typography variant="subtitle1" component="div">
                                        Contact
                                    </Typography>
                                </Grid>
                                <Grid item xs={2}>
                                    <Typography variant="subtitle1" component="div">
                                        Doctor Watch
                                    </Typography>
                                </Grid>
                            </Grid>
                        </Grid>
                        <Grid item xs={3}>
                            <Typography variant="subtitle1" component="div">
                                @Dentist Watch | All Rights Reserved
                            </Typography>
                        </Grid>
                    </Grid>
                </Toolbar>
            </AppBar>
        </Box>
    )
}
