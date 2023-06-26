import React from "react";
import AppBar from "@mui/material/AppBar";
import Box from "@mui/material/Box";
import Toolbar from "@mui/material/Toolbar";
import Typography from "@mui/material/Typography";
import {Grid, Link} from "@mui/material";

export default function Footer({context}) {
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
                                    <Typography textAlign="center">
                                        <Link sx={{color: 'white'}}
                                              href={`www.${context.alternativeSite.toLowerCase().trim()}.org`}>
                                            {context.alternativeSite}
                                        </Link>
                                    </Typography>
                                </Grid>
                            </Grid>
                        </Grid>
                        <Grid item xs={3}>
                            <Typography variant="subtitle1" component="div">
                                @{context.projectName} | All Rights Reserved
                            </Typography>
                        </Grid>
                    </Grid>
                </Toolbar>
            </AppBar>
        </Box>
    )
}
