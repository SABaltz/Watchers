import React from 'react'
import Box from "@mui/material/Box";

let doctor1 = require('../static/doctor1.jpg')
let dentist1 = require('../static/dentist1.jpg')

export default function HomePage({context}) {
    let image = context.projectName === "Dentist Watch" ? dentist1 : doctor1
    return (
        <>
            <Box
                sx={{
                    // backgroundImage: 'url(' + context.projectName === "Dentist Watch" ? dentist1 : doctor1 + ')',
                    backgroundImage: 'url(' + image + ')',
                    backgroundRepeat: "no-repeat",
                    backgroundPosition: 'center',
                    backgroundSize: 'cover',
                    width: '100vw',
                    height: '100vh'
                }}
            >

            </Box>
        </>
    )
}
